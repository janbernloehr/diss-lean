import NLS.ZakharovShabat.SourceSobolevCompactStep

/-!
# Compact inverse Sobolev regularity from a common actual-gap majorant

Finite iteration reaches every nonnegative order strictly below the available
gap order. Each step spends part of its gain to retain a continuous compact
realization of the entire original source family.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A compact real-source family dominated by one gap sequence of order S
has a continuous exact realization at every nonnegative order s<S. Its
entire range is compact in the stronger finite-p source norm. -/
theorem exists_compact_source_sobolev_family_of_gap_majorant
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [Nonempty T]
    (φ : T → realTypeSourceSubmodule p) (hφ : Continuous φ)
    (S s : ℝ) (hs : 0 ≤ s) (hsS : s < S)
    (Γ : Coeff p) (hΓ : Memℓp (fun n : ℤ => (Weight.sobolev S n:ℂ)*Γ n) p)
    (hgap : ∀ x n, ‖sourcePeriodicGapDisplacement hp hp1 (φ x).val n‖ ≤ ‖Γ n‖) :
    ∃ B : T → CoeffPair p, Continuous B ∧
      (∀ x n, (B x).fst n = (Weight.sobolev s n:ℂ)*(φ x).val.fst n ∧
        (B x).snd n = (Weight.sobolev s n:ℂ)*(φ x).val.snd n) ∧
      IsCompact (range B) := by
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · subst s
    refine ⟨fun x => (φ x).val,continuous_subtype_val.comp hφ,?_,
      isCompact_range (continuous_subtype_val.comp hφ)⟩
    intro x n
    simp only [Weight.sobolev_zero_apply,Complex.ofReal_one,one_mul,and_self]
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have hp0 : 0 < p.toReal := zero_lt_one.trans hpR
  let α := min 1 (p.toReal-1)
  have hα : 0 < α := lt_min (by norm_num) (by linarith only [hpR])
  obtain ⟨K,hK⟩ := exists_nat_gt (max (2*s*p.toReal/α) (s/(S-s)))
  have hKr : 0 < (K:ℝ) :=
    (div_pos (mul_pos (mul_pos (by norm_num) hs0) hp0) hα).trans
      ((le_max_left _ _).trans_lt hK)
  let σ := s/(K:ℝ)
  have hσ : 0 < σ := div_pos hs0 hKr
  have hKσ : (K:ℝ)*σ = s := by dsimp [σ]; field_simp
  have hσS : σ < S-s := by
    apply (div_lt_iff₀ hKr).mpr
    have h := (div_lt_iff₀ (sub_pos.mpr hsS)).mp ((le_max_right _ _).trans_lt hK)
    nlinarith only [h]
  have hσp : (2*σ)*p.toReal < min 1 (p.toReal-1) := by
    have h := (div_lt_iff₀ hα).mp ((le_max_left _ _).trans_lt hK)
    have he : (2*σ)*p.toReal = (2*s*p.toReal)/(K:ℝ) := by dsimp [σ]; ring
    rw [he]
    exact (div_lt_iff₀ hKr).mpr (by dsimp only [α] at h; nlinarith only [h])
  have hall (k : ℕ) (hk : k ≤ K) :
      ∃ A : T → CoeffPair p, Continuous A ∧
        (∀ x n, (A x).fst n = (Weight.sobolev ((k:ℝ)*σ) n:ℂ)*(φ x).val.fst n ∧
          (A x).snd n = (Weight.sobolev ((k:ℝ)*σ) n:ℂ)*(φ x).val.snd n) ∧
        IsCompact (range A) := by
    induction k with
    | zero =>
      refine ⟨fun x => (φ x).val,continuous_subtype_val.comp hφ,?_,
        isCompact_range (continuous_subtype_val.comp hφ)⟩
      intro x n
      simp only [Nat.cast_zero,zero_mul,Weight.sobolev_zero_apply,Complex.ofReal_one,one_mul,and_self]
    | succ k ih =>
      obtain ⟨A,hA,hAc,_⟩ := ih (by omega)
      have hkr : (k:ℝ)+1 ≤ K := by exact_mod_cast hk
      have hle : (k:ℝ)*σ+2*σ ≤ S := by
        have h := mul_le_mul_of_nonneg_right hkr hσ.le
        nlinarith only [h,hKσ,hσS]
      have hΓk : Memℓp (fun n : ℤ => (Weight.sobolev ((k:ℝ)*σ+2*σ) n:ℂ)*Γ n) p := by
        apply hΓ.mono'
        intro n
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
          abs_of_pos ((Weight.sobolev ((k:ℝ)*σ+2*σ)).positive n),
          abs_of_pos ((Weight.sobolev S).positive n)]
        exact mul_le_mul_of_nonneg_right (Weight.sobolev_mono hle n) (norm_nonneg _)
      obtain ⟨B,hB,hBc,hcomp⟩ := exists_compact_source_sobolev_step hp hp1 φ hφ
        ((k:ℝ)*σ) (2*σ) σ (by positivity) (by positivity) (by linarith only [hσ]) hσp
        A hA hAc Γ hΓk hgap
      refine ⟨B,hB,?_,hcomp⟩
      simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using hBc
  simpa only [hKσ] using hall K le_rfl

end NLS.ZakharovShabat
