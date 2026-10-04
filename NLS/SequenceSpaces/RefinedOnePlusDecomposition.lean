import NLS.SequenceSpaces.OnePlus

/-! # A fixed mixed decomposition from simultaneous refined bounds

When a sequence belongs locally uniformly to every lr with r > 1 and
r >= t, it has a single lt + l(1+) decomposition. The components are
chosen before the projection exponent, not separately for each lr.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff

/-- Construct one mixed pair of maps with locally uniform bounds for
every finite projection of its genuine l(1+) component. -/
theorem exists_onePlus_decomposition_of_refined {E : Type*} (T : Set E)
    (f : E → ℤ → ℂ) {t : ℝ≥0∞} (ht : t ≠ ⊤)
    (hb : ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → t ≤ r →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ∃ b : Coeff r,
        (∀ n, b n = f ψ n) ∧ ‖b‖ ≤ C) :
    ∃ a : E → Coeff t, ∃ b : E → CoeffOnePlus,
      (∀ ψ ∈ T, ∀ n, f ψ n = a ψ n + (b ψ).1 n) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ‖a ψ‖ ≤ C) ∧
      ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ T, ‖CoeffOnePlus.toCoeff q hq1 hq (b ψ)‖ ≤ C := by
  classical
  by_cases ht1 : 1 < t
  · obtain ⟨C,hC,hb⟩ := hb t ht ht1 le_rfl
    let a : E → Coeff t := fun ψ => if hψ : ψ ∈ T then Classical.choose (hb ψ hψ) else 0
    refine ⟨a,fun _ => 0,?_,⟨C,hC,?_⟩,?_⟩
    · intro ψ hψ n
      change f ψ n = a ψ n + 0
      simpa only [a,dif_pos hψ,add_zero] using
        ((Classical.choose_spec (hb ψ hψ)).1 n).symm
    · intro ψ hψ
      simpa only [a,dif_pos hψ] using (Classical.choose_spec (hb ψ hψ)).2
    · intro q hq1 hq
      exact ⟨0,le_rfl,fun _ _ => by change ‖(0 : Coeff q)‖ ≤ 0; simp⟩
  · have hmem (ψ : E) (hψ : ψ ∈ T) (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤) :
        Memℓp (f ψ) q := by
      obtain ⟨_,_,hc⟩ := hb q hq hq1 ((le_of_not_gt ht1).trans hq1.le)
      obtain ⟨c,hc,_⟩ := hc ψ hψ
      have he : (fun n => c n) = f ψ := funext hc
      rw [← he]
      exact lp.memℓp c
    let b : E → CoeffOnePlus := fun ψ => if hψ : ψ ∈ T then ⟨f ψ,hmem ψ hψ⟩ else 0
    refine ⟨fun _ => 0,b,?_,⟨0,le_rfl,fun _ _ => by simp⟩,?_⟩
    · intro ψ hψ n
      simp only [b,dif_pos hψ,lp.coeFn_zero,Pi.zero_apply,zero_add]
    · intro q hq1 hq
      obtain ⟨C,hC,hc⟩ := hb q hq hq1 ((le_of_not_gt ht1).trans hq1.le)
      refine ⟨C,hC,?_⟩
      intro ψ hψ
      obtain ⟨c,hc,hn⟩ := hc ψ hψ
      have he : CoeffOnePlus.toCoeff q hq1 hq (b ψ) = c := by
        ext n
        simpa only [CoeffOnePlus.toCoeff_apply,b,dif_pos hψ] using (hc n).symm
      rwa [he]

end NLS.Coeff
