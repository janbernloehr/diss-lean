import NLS.SequenceSpaces.PositiveOperatorDiagonal
import Mathlib.Analysis.Normed.Operator.Banach
import NLS.FunctionalAnalysis.NonzeroSequenceLowerBound

/-! A positive-index operator diagonal bounded away from zero is an
actual Banach isomorphism. The inverse divides by the original entries. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.LpSequence

theorem exists_positiveOperatorDiagonal_equiv_of_lowerBound
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ m : ℕ+, δ ≤ ‖T (lp.single 2 m 1) m‖) :
    ∃ e : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
      e.toContinuousLinearMap = positiveOperatorDiagonal T ∧
      ∀ a m, e.symm a m = (T (lp.single 2 m 1) m)⁻¹*a m := by
  let D := positiveOperatorDiagonal T
  let f : ℕ+ → ℂ := fun m => T (lp.single 2 m 1) m
  have hf (m : ℕ+) : f m ≠ 0 := fun h => by
    have hh := hlower m
    change δ ≤ ‖f m‖ at hh
    rw [h,norm_zero] at hh
    exact (not_lt_of_ge hh) hδ
  have hi (m : ℕ+) : ‖(f m)⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ (hδ.trans_le (hlower m)) hδ).2 (hlower m)
  have hinj : Function.Injective D := by
    intro a b hab
    ext m
    apply mul_left_cancel₀ (hf m)
    have h := congrArg (fun v : lp (fun _ : ℕ+ => ℂ) 2 => v m) hab
    simpa only [D,positiveOperatorDiagonal_apply,f] using h
  have hsurj : Function.Surjective D := by
    intro a
    let b : lp (fun _ : ℕ+ => ℂ) 2 := ⟨fun m => (f m)⁻¹*a m,by
      apply ((lp.memℓp a).norm.const_mul δ⁻¹).mono
      intro m
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hi m) (norm_nonneg _)⟩
    refine ⟨b,?_⟩
    ext m
    change positiveOperatorDiagonal T b m = a m
    rw [positiveOperatorDiagonal_apply]
    change f m*((f m)⁻¹*a m) = a m
    rw [← mul_assoc,mul_inv_cancel₀ (hf m),one_mul]
  let e := ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
  refine ⟨e,rfl,?_⟩
  intro a m
  apply mul_left_cancel₀ (hf m)
  have he := congrArg (fun v : lp (fun _ : ℕ+ => ℂ) 2 => v m) (e.apply_symm_apply a)
  change D (e.symm a) m = a m at he
  rw [positiveOperatorDiagonal_apply] at he
  change f m*e.symm a m = f m*((f m)⁻¹*a m)
  rw [← mul_assoc,mul_inv_cancel₀ (hf m),one_mul]
  exact he

theorem exists_positiveOperatorDiagonal_equiv_of_tendsto_one
    (T : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2)
    (hn : ∀ m : ℕ+, T (lp.single 2 m 1) m ≠ 0)
    (ht : Tendsto (fun j : ℕ => T (lp.single 2 ⟨j+1,by omega⟩ 1) ⟨j+1,by omega⟩) atTop (𝓝 1)) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ m : ℕ+, δ ≤ ‖T (lp.single 2 m 1) m‖) ∧
      ∃ e : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
        e.toContinuousLinearMap = positiveOperatorDiagonal T ∧
        ∀ a m, e.symm a m = (T (lp.single 2 m 1) m)⁻¹*a m := by
  obtain ⟨δ,hδ,hbound⟩ := NLS.FunctionalAnalysis.exists_positive_lower_norm_of_tendsto
    (fun j : ℕ => T (lp.single 2 ⟨j+1,by omega⟩ 1) ⟨j+1,by omega⟩) (1:ℂ) one_ne_zero
    (fun j => hn ⟨j+1,by omega⟩) ht
  have hlower (m : ℕ+) : δ ≤ ‖T (lp.single 2 m 1) m‖ := by
    have he : (⟨(m:ℕ)-1+1,by omega⟩:ℕ+) = m := Subtype.ext (by change (m:ℕ)-1+1 = (m:ℕ); have := m.pos; omega)
    simpa only [he] using hbound ((m:ℕ)-1)
  obtain ⟨e,he,hinv⟩ := exists_positiveOperatorDiagonal_equiv_of_lowerBound T δ hδ hlower
  exact ⟨δ,hδ,hlower,e,he,hinv⟩

end NLS.LpSequence
