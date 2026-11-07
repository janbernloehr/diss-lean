import NLS.SequenceSpaces.GeometricTailMajorant

/-!
# A common Sobolev norm bound from a common geometric tail envelope

No continuity of the stronger realizations is assumed. The uniform tail
budget constructs the exact weighted coefficient family and bounds its
complete norm, including the finite central block.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Uniform geometric tail energies and an original norm bound construct
the exact Sobolev coefficient family with one common full norm bound. -/
theorem exists_uniform_sobolev_family_of_geometric_tail_envelope
    (hp : p ≠ ⊤) {T : Type*} (a : T → Coeff p) (R : ℝ) (hR : 0 ≤ R)
    (ha : ∀ t, ‖a t‖ ≤ R) (M : ℕ) (hM : 0 < M) (s : ℝ) (hs : 0 ≤ s)
    (V : ℕ → ℝ) (hV : ∀ k, 0 ≤ V k)
    (hVs : Summable (fun k => ((4:ℝ)^(s*p.toReal))^k*V k))
    (ht : ∀ t k, ‖fourierTail (4^k*M) (a t)‖^p.toReal ≤ V k) :
    ∃ F : T → Coeff p, (∀ t n, F t n = (Weight.sobolev s n:ℂ)*a t n) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖F t‖ ≤ C := by
  have hpR : 1 ≤ p.toReal := (ENNReal.toReal_le_toReal (by simp) hp).mpr (Fact.out : 1 ≤ p)
  have hp0 : 0 < p.toReal := zero_lt_one.trans_le hpR
  let r := (4:ℝ)^(s*p.toReal)
  let g := fun k => r^k*V k
  let D := (1+4*(M:ℝ))^(s*p.toReal)
  have hg : Summable g := hVs
  have hg0 : ∀ k, 0 ≤ g k := fun k => mul_nonneg (by dsimp [r]; positivity) (hV k)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbridge (t : T) :=
    summable_sobolev_tsum_le_of_geometric_tail_majorant (fun n => ‖a t n‖^p.toReal)
      (fun n => Real.rpow_nonneg (norm_nonneg _) _) ((a t).property.summable hp0)
      M hM (s*p.toReal) (mul_nonneg hs hp0.le) g hg (by
        intro k
        have he : (∑' n : ℤ, if 4^k*M ≤ n.natAbs then ‖a t n‖^p.toReal else 0) =
            ‖fourierTail (4^k*M) (a t)‖^p.toReal := by
          rw [lp.norm_rpow_eq_tsum hp0]
          apply tsum_congr
          intro n
          rw [fourierTail_apply]
          split_ifs <;> simp only [norm_zero,Real.zero_rpow hp0.ne']
        rw [he]
        exact mul_le_mul_of_nonneg_left (ht t k) (by positivity))
  have he (t : T) (n : ℤ) :
      ‖(Weight.sobolev s n:ℂ)*a t n‖^p.toReal =
        (1+|(n:ℝ)|)^(s*p.toReal)*‖a t n‖^p.toReal := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ((Weight.sobolev s).positive n),
      Real.mul_rpow ((Weight.sobolev s).positive n).le (norm_nonneg _),
      Weight.sobolev_apply,← Real.rpow_mul (by positivity)]
  have hmem (t : T) : Memℓp (fun n => (Weight.sobolev s n:ℂ)*a t n) p := by
    apply memℓp_gen
    exact (hbridge t).1.congr (fun n => (he t n).symm)
  let F : T → Coeff p := fun t => ⟨_,hmem t⟩
  let L := D*(R^p.toReal+∑' k, g k)
  have hL : 0 ≤ L := mul_nonneg hD (add_nonneg (Real.rpow_nonneg hR _) (tsum_nonneg hg0))
  have hbudget (t : T) : ‖F t‖^p.toReal ≤ L := by
    rw [lp.norm_rpow_eq_tsum hp0]
    have hsum : (∑' n, ‖a t n‖^p.toReal) ≤ R^p.toReal := by
      rw [← lp.norm_rpow_eq_tsum hp0]
      exact Real.rpow_le_rpow (norm_nonneg _) (ha t) hp0.le
    have h := (hbridge t).2.trans (mul_le_mul_of_nonneg_left
      (add_le_add hsum le_rfl) hD)
    exact (tsum_congr fun n => he t n).trans_le h
  refine ⟨F,fun _ _ => rfl,L+1,by linarith only [hL],fun t => ?_⟩
  by_cases hsmall : ‖F t‖ ≤ 1
  · exact hsmall.trans (by linarith only [hL])
  · exact (Real.self_le_rpow_of_one_le (by linarith only [hsmall]) hpR).trans
      ((hbudget t).trans (by linarith))

end NLS.Coeff
