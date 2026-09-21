import NLS.ZakharovShabat.RealGapProductSigns

/-!
# Real spectral gaps characterized by the discriminant
On the real axis the closed canonical gaps are exactly the set where
|Delta| is at least two. Equality occurs exactly at periodic endpoints,
and the open gap interiors are exactly the set where |Delta| exceeds two.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Reality identifies the norm square with the square of the real part. -/
theorem norm_canonicalDiscriminant_sq_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (x : ℝ) :
    ‖canonicalDiscriminant hp φ x‖^2 = (canonicalDiscriminant hp φ x).re^2 := by
  have h := Complex.sq_norm_sub_sq_re (canonicalDiscriminant hp φ x)
  rw [canonicalDiscriminant_im_eq_zero_of_realType hp hp1 φ heven hreal] at h
  nlinarith

/-- The real level equation is exhausted by the canonical endpoint slots. -/
theorem discriminant_re_sq_eq_four_iff_canonicalEndpoint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (x : ℝ) :
    (canonicalDiscriminant hp φ x).re^2 = 4 ↔ ∃ n : ℤ,
      x = (canonicalPeriodicLeft hp hp1 φ heven n).re ∨ x = (canonicalPeriodicRight hp hp1 φ heven n).re := by
  have hd : canonicalDiscriminant hp φ x = ((canonicalDiscriminant hp φ x).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [canonicalDiscriminant_im_eq_zero_of_realType hp hp1 φ heven hreal]
  have heq : (canonicalDiscriminant hp φ x).re^2 = 4 ↔ (canonicalDiscriminant hp φ x)^2 = 4 := by
    rw [hd]
    norm_cast
  rw [heq,canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 φ heven,
    canonicalPeriodicEndpoints_exhaustive hp hp1 φ heven]
  constructor
  · rintro ⟨n,hl | hr⟩
    · exact ⟨n,Or.inl (by simpa using (congrArg re hl).symm)⟩
    · exact ⟨n,Or.inr (by simpa using (congrArg re hr).symm)⟩
  · rintro ⟨n,hl | hr⟩
    · refine ⟨n,Or.inl (Complex.ext ?_ ?_)⟩
      · simpa using hl.symm
      · simpa using (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 φ heven hreal n).1
    · refine ⟨n,Or.inr (Complex.ext ?_ ?_)⟩
      · simpa using hr.symm
      · simpa using (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 φ heven hreal n).2

/-- Outside every closed real gap the discriminant square is strictly below four. -/
theorem discriminant_re_sq_lt_four_of_outside_canonicalGaps (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (x : ℝ)
    (hx : ∀ n : ℤ, x ∉ Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re) :
    (canonicalDiscriminant hp φ x).re^2 < 4 := by
  apply lt_of_le_of_ne (discriminant_re_sq_le_four_of_outside_canonicalGaps hp hp1 φ heven hreal x hx)
  intro he
  obtain ⟨n,hl | hr⟩ := (discriminant_re_sq_eq_four_iff_canonicalEndpoint hp hp1 φ heven hreal x).mp he
  · exact hx n (by rw [hl]; exact ⟨le_rfl,re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1 φ heven).2.1 n)⟩)
  · exact hx n (by rw [hr]; exact ⟨re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1 φ heven).2.1 n),le_rfl⟩)

/-- The closed canonical real gaps are exactly the points where the discriminant modulus is at least two. -/
theorem two_le_norm_discriminant_iff_mem_canonicalGap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (x : ℝ) :
    2 ≤ ‖canonicalDiscriminant hp φ x‖ ↔ ∃ n : ℤ,
      x ∈ Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re := by
  have hs := norm_canonicalDiscriminant_sq_of_realType hp hp1 φ heven hreal x
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have he := discriminant_re_sq_lt_four_of_outside_canonicalGaps hp hp1 φ heven hreal x hn
    nlinarith
  · rintro ⟨n,hx⟩
    have he := discriminant_re_sq_ge_four_of_mem_canonicalGap hp hp1 φ heven hreal n x hx
    nlinarith [norm_nonneg (canonicalDiscriminant hp φ x)]

/-- The strict middle strip is the complement of all closed canonical real gaps. -/
theorem norm_discriminant_lt_two_iff_outside_canonicalGaps (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (x : ℝ) :
    ‖canonicalDiscriminant hp φ x‖ < 2 ↔ ∀ n : ℤ,
      x ∉ Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re := by
  simpa only [not_le,not_exists] using not_congr (two_le_norm_discriminant_iff_mem_canonicalGap hp hp1 φ heven hreal x)

/-- Modulus two occurs exactly at an endpoint, with collapsed endpoint pairs allowed. -/
theorem norm_discriminant_eq_two_iff_canonicalEndpoint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (x : ℝ) :
    ‖canonicalDiscriminant hp φ x‖ = 2 ↔ ∃ n : ℤ,
      x = (canonicalPeriodicLeft hp hp1 φ heven n).re ∨ x = (canonicalPeriodicRight hp hp1 φ heven n).re := by
  rw [← discriminant_re_sq_eq_four_iff_canonicalEndpoint hp hp1 φ heven hreal x,
    ← norm_canonicalDiscriminant_sq_of_realType hp hp1 φ heven hreal x]
  constructor <;> intro h <;> nlinarith [norm_nonneg (canonicalDiscriminant hp φ x)]

/-- The discriminant modulus is strictly greater than two inside each open real gap. -/
theorem two_lt_norm_discriminant_of_mem_canonicalGap_interior (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re) :
    2 < ‖canonicalDiscriminant hp φ x‖ := by
  have hclosed : x ∈ Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re := ⟨hx.1.le,hx.2.le⟩
  apply lt_of_le_of_ne ((two_le_norm_discriminant_iff_mem_canonicalGap hp hp1 φ heven hreal x).mpr ⟨n,hclosed⟩)
  intro he
  obtain ⟨m,hm⟩ := (norm_discriminant_eq_two_iff_canonicalEndpoint hp hp1 φ heven hreal x).mp he.symm
  by_cases hmn : m = n
  · subst m
    rcases hm with hm | hm <;> linarith [hx.1,hx.2]
  · have hmclosed : x ∈ Icc (canonicalPeriodicLeft hp hp1 φ heven m).re (canonicalPeriodicRight hp hp1 φ heven m).re := by
      have ho := re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1 φ heven).2.1 m)
      rcases hm with hm | hm <;> rw [hm] <;> exact ⟨by linarith,by linarith⟩
    exact Set.disjoint_left.mp (canonicalPeriodicGaps_disjoint hp hp1 φ heven hreal hmn) hmclosed hclosed

/-- The open canonical real gaps are exactly the points with discriminant modulus greater than two. -/
theorem two_lt_norm_discriminant_iff_mem_canonicalGap_interior (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (x : ℝ) :
    2 < ‖canonicalDiscriminant hp φ x‖ ↔ ∃ n : ℤ,
      x ∈ Ioo (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re := by
  constructor
  · intro h
    obtain ⟨n,hx⟩ := (two_le_norm_discriminant_iff_mem_canonicalGap hp hp1 φ heven hreal x).mp h.le
    have hne : ¬ ∃ m : ℤ, x = (canonicalPeriodicLeft hp hp1 φ heven m).re ∨ x = (canonicalPeriodicRight hp hp1 φ heven m).re := by
      intro he
      have hnorm := (norm_discriminant_eq_two_iff_canonicalEndpoint hp hp1 φ heven hreal x).mpr he
      linarith
    refine ⟨n,lt_of_le_of_ne hx.1 ?_,lt_of_le_of_ne hx.2 ?_⟩
    · intro he; exact hne ⟨n,Or.inl he.symm⟩
    · intro he; exact hne ⟨n,Or.inr he⟩
  · rintro ⟨n,hx⟩
    exact two_lt_norm_discriminant_of_mem_canonicalGap_interior hp hp1 φ heven hreal n x hx

end NLS.ZakharovShabat
