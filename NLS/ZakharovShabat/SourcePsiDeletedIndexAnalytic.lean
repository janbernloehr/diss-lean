import NLS.ZakharovShabat.SourcePsiDeletedIndexEquation

/-!
# Lemma 12.4 on the literal deleted-index spaces

The exact sequence-space isometry transports joint analyticity to the
source's retained-index interface. Its norm and power-sum bounds use one
ambient root/source neighborhood before all deleted indices, with the
same constants and the same original source domain.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal retained-index equation is jointly complex analytic on all of W. -/
theorem SourceLemma12_4Data.deletedIndexEquation_analytic
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (n : ℤ) :
    AnalyticOnNhd ℂ
      (fun t : CoeffPair p × DeletedIndexCoeff p n => sourcePsiDeletedIndexEquation hp hp1 n t.1 t.2)
      (W ×ˢ univ) := by
  intro t ht
  let e := (DeletedCoeff.indexEquiv hp n).toContinuousLinearEquiv
  have hi : AnalyticAt ℂ
      (fun q : CoeffPair p × DeletedIndexCoeff p n => (q.1,e.symm q.2)) t :=
    analyticAt_fst.prod ((e.symm.analyticAt t.2).comp analyticAt_snd)
  have ha := (H.analytic n (t.1,e.symm t.2) ⟨ht.1,mem_univ _⟩).comp
    (f := fun q : CoeffPair p × DeletedIndexCoeff p n => (q.1,e.symm q.2)) hi
  exact (e.analyticAt _).comp ha

/-- Restriction of scalars gives the real analyticity printed in Lemma 12.4. -/
theorem SourceLemma12_4Data.deletedIndexEquation_real_analytic
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (n : ℤ) :
    AnalyticOnNhd ℝ
      (fun t : CoeffPair p × DeletedIndexCoeff p n => sourcePsiDeletedIndexEquation hp hp1 n t.1 t.2)
      (W ×ˢ univ) :=
  fun t ht => (H.deletedIndexEquation_analytic n t ht).restrictScalars (𝕜 := ℝ)

/-- The literal retained-coordinate power sum equals the existing zero-at-n sum exactly. -/
theorem sum_rpow_sourcePsiDeletedIndexEquation (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) (a : DeletedIndexCoeff p n) :
    (∑' m : {m : ℤ // m ≠ n}, ‖sourcePsiDeletedIndexEquation hp hp1 n ψ a m‖^p.toReal) =
      ∑' m : ℤ,
        ‖(sourcePsiOriginalEquation hp hp1 n ((DeletedCoeff.indexEquiv hp n).symm a) ψ : Coeff p) m‖^p.toReal := by
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  rw [← lp.norm_rpow_eq_tsum hp0,← lp.norm_rpow_eq_tsum hp0]
  exact congrArg (fun x : ℝ => x^p.toReal)
    (norm_sourcePsiDeletedIndexEquation hp hp1 n ψ a)

/-- One ambient neighborhood and one norm bound serve every deleted-index space. -/
theorem SourceLemma12_4Data.deletedIndexEquation_locally_uniform
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, ∀ a : DeletedIndexCoeff p n, ∀ ψ : CoeffPair p,
        (((DeletedCoeff.indexEquiv hp n).symm a : Coeff p),ψ) ∈ U →
          ‖sourcePsiDeletedIndexEquation hp hp1 n ψ a‖ ≤ C := by
  obtain ⟨U,hU,hbase,hUW,C,hC,hbound⟩ := H.locally_uniform φ hφ a₀
  refine ⟨U,hU,hbase,hUW,C,hC,?_⟩
  intro n a ψ ha
  rw [norm_sourcePsiDeletedIndexEquation]
  exact hbound n ((DeletedCoeff.indexEquiv hp n).symm a) ψ ha

/-- The printed strict power-sum estimate, with the sum indexed literally by m ≠ n. -/
theorem SourceLemma12_4Data.deletedIndexEquation_power_sum
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ, ∀ a : DeletedIndexCoeff p n, ∀ ψ : CoeffPair p,
        (((DeletedCoeff.indexEquiv hp n).symm a : Coeff p),ψ) ∈ U →
          (∑' m : {m : ℤ // m ≠ n}, ‖sourcePsiDeletedIndexEquation hp hp1 n ψ a m‖^p.toReal) < C := by
  obtain ⟨U,hU,hbase,hUW,C,hC,hbound⟩ := H.power_sum φ hφ a₀
  refine ⟨U,hU,hbase,hUW,C,hC,?_⟩
  intro n a ψ ha
  rw [sum_rpow_sourcePsiDeletedIndexEquation]
  exact hbound n ((DeletedCoeff.indexEquiv hp n).symm a) ψ ha

end NLS.ZakharovShabat
