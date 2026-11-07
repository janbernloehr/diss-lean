import NLS.KdV.HillProductCoordinateVariation
import NLS.ZakharovShabat.SourcePsiDeletedProductNonzero

/-! The literal retained Hill product has EXACTLY its retained energy
zeros for ANY complex full-l2 data, without reality or placement. It
is never identically zero. The normalization scalar is not assumed. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem displacedRoots_hillEnergyProductEmbedding_positive (n m : ℕ+) (E : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) :
    displacedRoots (hillEnergyProductEmbedding n (E,d)) ((m:ℕ):ℤ) =
      if m = n then (Real.pi:ℂ)*(m:ℕ) else (hillEnergySequenceZero m d-E)/((Real.pi:ℂ)*(m:ℕ)) := by
  unfold displacedRoots
  rw [hillEnergyProductEmbedding_positive]
  simp only [Int.cast_natCast]
  by_cases hmn : m = n
  · simp only [if_pos hmn,add_zero]
  · simp only [if_neg hmn,hillEnergySequenceZero]
    have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hm : ((m:ℕ):ℂ) ≠ 0 := by exact_mod_cast m.ne_zero
    field_simp [hpi,hm]
    ring

theorem hillEnergySequenceProduct_ne_zero_of_off_roots (n : ℕ+) (E : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (hother : ∀ m : ℕ+, m ≠ n → E ≠ hillEnergySequenceZero m d) :
    hillEnergySequenceProduct n (E,d) ≠ 0 := by
  apply jointDeletedSingleSpectralProduct_ne_zero_of_off_other (by norm_num) (by norm_num) 0 0
  intro k hk hz
  have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases hkpos : 0 < k
  · let m : ℕ+ := ⟨k.toNat,by omega⟩
    have hkm : k = ((m:ℕ):ℤ) := by change k = (k.toNat:ℤ); omega
    rw [hkm,displacedRoots_hillEnergyProductEmbedding_positive] at hz
    by_cases hmn : m = n
    · rw [if_pos hmn] at hz
      exact (mul_ne_zero hpi (by exact_mod_cast m.ne_zero)) hz.symm
    · rw [if_neg hmn] at hz
      have hnum : hillEnergySequenceZero m d-E = 0 := (div_eq_zero_iff.mp hz.symm).resolve_right
        (mul_ne_zero hpi (by exact_mod_cast m.ne_zero))
      exact hother m hmn (sub_eq_zero.mp hnum).symm
  · unfold displacedRoots at hz
    rw [hillEnergyProductEmbedding_nonpos n (E,d) k (by omega),add_zero] at hz
    exact (mul_ne_zero hpi (Int.cast_ne_zero.mpr hk)) hz.symm

theorem hillEnergySequenceProduct_eq_zero_iff (n : ℕ+) (E : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergySequenceProduct n (E,d) = 0 ↔ ∃ m : ℕ+, m ≠ n ∧ E = hillEnergySequenceZero m d := by
  constructor
  · intro hz
    by_contra h
    push Not at h
    exact hillEnergySequenceProduct_ne_zero_of_off_roots n E d h hz
  · rintro ⟨m,hmn,rfl⟩
    exact hillEnergySequenceProduct_retained_root n m hmn d

theorem exists_hillEnergySequenceProduct_ne_zero (n : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    ∃ E : ℂ, hillEnergySequenceProduct n (E,d) ≠ 0 := by
  obtain ⟨E,hE⟩ : ∃ E : ℂ, E ∉ range (fun m : ℕ+ => hillEnergySequenceZero m d) :=
    ((Set.countable_range (fun m : ℕ+ => hillEnergySequenceZero m d)).dense_compl ℂ).nonempty
  exact ⟨E,hillEnergySequenceProduct_ne_zero_of_off_roots n E d (fun m _ he => hE ⟨m,he.symm⟩)⟩

theorem hillEnergySequenceProduct_energy_ne_zero (n : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    (fun E => hillEnergySequenceProduct n (E,d)) ≠ 0 := by
  obtain ⟨E,hE⟩ := exists_hillEnergySequenceProduct_ne_zero n d
  exact fun h => hE (congrFun h E)

end NLS.KdV
