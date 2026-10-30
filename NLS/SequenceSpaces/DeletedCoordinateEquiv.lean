import NLS.SequenceSpaces.DeletedCoordinate

/-!
# The literal sequence space with one integer removed

Restriction identifies the closed zero-at-n model with lp on the subtype
of retained integers. Its inverse extends by zero, and the original lp
norm is preserved exactly for every finite Banach exponent.
-/

noncomputable section
open scoped ENNReal
namespace NLS
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal coefficient space indexed by integers other than n. -/
abbrev DeletedIndexCoeff (p : ℝ≥0∞) (n : ℤ) :=
  lp (fun _ : {m : ℤ // m ≠ n} => ℂ) p

namespace DeletedCoeff

/-- Restrict the zero-at-n model to its retained indices. -/
def restrict (hp : p ≠ ⊤) (n : ℤ) (a : DeletedCoeff p n) : DeletedIndexCoeff p n :=
  ⟨fun m => (a : Coeff p) m.val, memℓp_gen
    (((lp.memℓp (a : Coeff p)).summable
      (ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp)).subtype
        (fun m => m ≠ n))⟩

/-- Extend the literal punctured-index sequence by zero at the omitted index. -/
def extend (hp : p ≠ ⊤) (n : ℤ) (a : DeletedIndexCoeff p n) : DeletedCoeff p n := by
  classical
  let f : ℤ → ℂ := fun m => if h : m ≠ n then a ⟨m,h⟩ else 0
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hs : Summable ((fun m => ‖f m‖ ^ p.toReal) ∘
      (Subtype.val : {m : ℤ // m ≠ n} → ℤ)) := by
    convert (lp.memℓp a).summable hp0 using 1
    funext m
    simp only [Function.comp_apply,f,dif_pos m.property]
  have hi : Summable ({m : ℤ | m ≠ n}.indicator (fun m => ‖f m‖ ^ p.toReal)) :=
    (summable_subtype_iff_indicator (s := {m : ℤ | m ≠ n})
      (f := fun m => ‖f m‖ ^ p.toReal)).mp hs
  have hf : Memℓp f p := memℓp_gen (by
    convert hi using 1
    funext m
    by_cases hm : m ≠ n
    · exact (Set.indicator_of_mem (s := {m : ℤ | m ≠ n}) hm
        (fun m => ‖f m‖ ^ p.toReal)).symm
    · rw [Set.indicator_of_notMem (s := {m : ℤ | m ≠ n}) hm]
      simp [hm,f,hp0.ne'])
  exact ⟨⟨f,hf⟩,by change f n = 0; simp [f]⟩

@[simp] theorem restrict_apply (hp : p ≠ ⊤) (n : ℤ) (a : DeletedCoeff p n)
    (m : {m : ℤ // m ≠ n}) : restrict hp n a m = (a : Coeff p) m.val := rfl

@[simp] theorem extend_apply_same (hp : p ≠ ⊤) (n : ℤ) (a : DeletedIndexCoeff p n) :
    ((extend hp n a : DeletedCoeff p n) : Coeff p) n = 0 := by
  simp [extend]

theorem extend_apply_other (hp : p ≠ ⊤) (n m : ℤ) (hm : m ≠ n)
    (a : DeletedIndexCoeff p n) :
    ((extend hp n a : DeletedCoeff p n) : Coeff p) m = a ⟨m,hm⟩ := by
  simp [extend,hm]

/-- The source's deleted-index space and the closed-kernel model have exactly the same norm. -/
def indexEquiv (hp : p ≠ ⊤) (n : ℤ) :
    DeletedCoeff p n ≃ₗᵢ[ℂ] DeletedIndexCoeff p n where
  toFun := restrict hp n
  invFun := extend hp n
  left_inv a := by
    apply Subtype.ext
    ext m
    by_cases hm : m = n
    · subst m
      exact (extend_apply_same hp n _).trans a.property.symm
    · rw [extend_apply_other hp n m hm,restrict_apply]
  right_inv a := by
    ext m
    exact extend_apply_other hp n m.val m.property a
  map_add' a b := by
    ext m
    rfl
  map_smul' z a := by
    ext m
    rfl
  norm_map' a := by
    have hp0 : 0 < p.toReal :=
      ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
    change ‖restrict hp n a‖ = ‖(a : Coeff p)‖
    rw [lp.norm_eq_tsum_rpow hp0,lp.norm_eq_tsum_rpow hp0]
    congr 1
    change (∑' m : {m : ℤ // m ≠ n}, ‖(a : Coeff p) m.val‖ ^ p.toReal) =
      ∑' m : ℤ, ‖(a : Coeff p) m‖ ^ p.toReal
    apply tsum_subtype_eq_of_support_subset (s := {m : ℤ | m ≠ n})
      (f := fun m : ℤ => ‖(a : Coeff p) m‖ ^ p.toReal)
    intro m hm
    change m ≠ n
    intro hmn
    subst m
    exact hm (by simp [show (a : Coeff p) n = 0 from a.property,hp0.ne'])

@[simp] theorem indexEquiv_apply (hp : p ≠ ⊤) (n : ℤ) (a : DeletedCoeff p n)
    (m : {m : ℤ // m ≠ n}) : indexEquiv hp n a m = (a : Coeff p) m.val := rfl

theorem indexEquiv_symm_apply_other (hp : p ≠ ⊤) (n m : ℤ) (hm : m ≠ n)
    (a : DeletedIndexCoeff p n) :
    (((indexEquiv hp n).symm a : DeletedCoeff p n) : Coeff p) m = a ⟨m,hm⟩ :=
  extend_apply_other hp n m hm a

end DeletedCoeff
end NLS
