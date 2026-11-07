import NLS.SequenceSpaces.PositiveInsertion
import NLS.SequenceSpaces.SandwichMajorant
import NLS.SequenceSpaces.PuncturedLattice
import NLS.ComplexAnalysis.ShiftedSquareRootBounds

/-! Independent inverse-index energy l2 data lift to principal positive
frequency displacements in l2. The norm estimate is GLOBAL, including
zeros and square-root cuts; analyticity on the open slit domain is proved
separately. The free lattice spacing is any positive real number. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.LpSequence

theorem norm_magnitude {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (d : lp (fun _ : ι => ℂ) p) : ‖magnitude d‖ = ‖d‖ := by
  apply le_antisymm
  · apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    intro m
    simp [magnitude]
  · apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    intro m
    simp [magnitude]

def positiveReciprocal : lp (fun _ : ℕ+ => ℂ) 2 :=
  positiveRestriction (Coeff.puncturedLattice 2 (by norm_num))

theorem positiveReciprocal_apply (m : ℕ+) : positiveReciprocal m = ((m:ℕ):ℂ)⁻¹ := by
  change Coeff.puncturedLattice 2 (by norm_num) ((m:ℕ):ℤ) = _
  rw [Coeff.puncturedLattice_apply,if_neg (by exact_mod_cast m.ne_zero)]
  simp only [Int.cast_natCast]

theorem norm_positiveReciprocal_le : ‖positiveReciprocal‖ ≤ 2 :=
  (norm_positiveRestriction_le _).trans Coeff.norm_puncturedLattice_two_le

def quadraticLatticeEnergy (α : ℝ) (m : ℕ+) (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  ((α:ℂ)*(m:ℕ))^2+(m:ℕ)*t.2 m+t.1

def positiveFrequencyError (α : ℝ) (m : ℕ+) (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  Complex.sqrt (quadraticLatticeEnergy α m t)-(α:ℂ)*(m:ℕ)

theorem norm_positiveFrequencyError_le (α : ℝ) (hα : 0 < α) (m : ℕ+)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) :
    ‖positiveFrequencyError α m t‖ ≤ α⁻¹*‖t.2 m‖+(‖t.1‖/α)*‖positiveReciprocal m‖ := by
  have hm : (0:ℝ) < (m:ℕ) := by exact_mod_cast m.pos
  have hz : 0 < ((α:ℂ)*(m:ℕ)).re := by simpa only [mul_re,ofReal_re,natCast_re,ofReal_im,natCast_im,mul_zero,sub_zero] using mul_pos hα hm
  have h : ‖positiveFrequencyError α m t‖ ≤ ‖((m:ℕ):ℂ)*t.2 m+t.1‖/((α:ℂ)*(m:ℕ)).re := by
    simpa only [positiveFrequencyError,quadraticLatticeEnergy,add_assoc] using
      NLS.ComplexAnalysis.norm_sqrt_sq_add_sub_le ((α:ℂ)*(m:ℕ)) ((m:ℕ)*t.2 m+t.1) hz
  calc
    _ ≤ ‖((m:ℕ):ℂ)*t.2 m+t.1‖/((α:ℂ)*(m:ℕ)).re := h
    _ ≤ (‖((m:ℕ):ℂ)*t.2 m‖+‖t.1‖)/((α:ℂ)*(m:ℕ)).re :=
      div_le_div_of_nonneg_right (norm_add_le _ _) hz.le
    _ = α⁻¹*‖t.2 m‖+(‖t.1‖/α)*‖positiveReciprocal m‖ := by
      rw [norm_mul,Complex.norm_natCast,positiveReciprocal_apply,norm_inv,Complex.norm_natCast]
      simp only [mul_re,ofReal_re,natCast_re,ofReal_im,natCast_im,mul_zero,sub_zero]
      field_simp

def positiveFrequencyMajorant (α : ℝ) (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : lp (fun _ : ℕ+ => ℂ) 2 :=
  (α⁻¹:ℂ) • magnitude t.2+((‖t.1‖/α):ℂ) • magnitude positiveReciprocal

theorem norm_positiveFrequencyMajorant_apply (α : ℝ) (hα : 0 < α)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (m : ℕ+) :
    ‖positiveFrequencyMajorant α t m‖ = α⁻¹*‖t.2 m‖+(‖t.1‖/α)*‖positiveReciprocal m‖ := by
  have he : positiveFrequencyMajorant α t m =
      ((α⁻¹*‖t.2 m‖+(‖t.1‖/α)*‖positiveReciprocal m‖:ℝ):ℂ) := by
    change (α⁻¹:ℂ)*(‖t.2 m‖:ℂ)+((‖t.1‖/α):ℂ)*(‖positiveReciprocal m‖:ℂ) = _
    push_cast; rfl
  rw [he,Complex.norm_real,Real.norm_of_nonneg (by positivity)]

theorem memlp_positiveFrequencyError (α : ℝ) (hα : 0 < α)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : Memℓp (fun m => positiveFrequencyError α m t) 2 :=
  (lp.memℓp (positiveFrequencyMajorant α t)).mono' (fun m => by
    rw [norm_positiveFrequencyMajorant_apply α hα]
    exact norm_positiveFrequencyError_le α hα m t)

def positiveFrequencyDisplacement (α : ℝ) (hα : 0 < α)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : lp (fun _ : ℕ+ => ℂ) 2 :=
  ⟨fun m => positiveFrequencyError α m t,memlp_positiveFrequencyError α hα t⟩

theorem positiveFrequencyDisplacement_apply (α : ℝ) (hα : 0 < α)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) (m : ℕ+) :
    positiveFrequencyDisplacement α hα t m = Complex.sqrt (quadraticLatticeEnergy α m t)-(α:ℂ)*(m:ℕ) := rfl

theorem norm_positiveFrequencyDisplacement_le (α : ℝ) (hα : 0 < α)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) :
    ‖positiveFrequencyDisplacement α hα t‖ ≤ α⁻¹*(‖t.2‖+2*‖t.1‖) := by
  have h : ‖positiveFrequencyDisplacement α hα t‖ ≤ ‖positiveFrequencyMajorant α t‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
    intro m
    rw [norm_positiveFrequencyMajorant_apply α hα]
    exact norm_positiveFrequencyError_le α hα m t
  have hαC : ‖(α⁻¹:ℂ)‖ = α⁻¹ := by simp [norm_inv,abs_of_pos hα]
  have hcC : ‖((‖t.1‖/α):ℂ)‖ = ‖t.1‖/α := by simp [abs_of_pos hα]
  have hM : ‖positiveFrequencyMajorant α t‖ ≤ α⁻¹*‖t.2‖+(‖t.1‖/α)*‖positiveReciprocal‖ := by
    have hb := norm_add_le ((α⁻¹:ℂ) • magnitude t.2) (((‖t.1‖/α):ℂ) • magnitude positiveReciprocal)
    simpa only [positiveFrequencyMajorant,norm_smul,norm_magnitude,hαC,hcC] using hb
  calc
    _ ≤ α⁻¹*‖t.2‖+(‖t.1‖/α)*‖positiveReciprocal‖ := h.trans hM
    _ ≤ α⁻¹*‖t.2‖+(‖t.1‖/α)*2 := add_le_add_right
      (mul_le_mul_of_nonneg_left norm_positiveReciprocal_le (div_nonneg (norm_nonneg _) hα.le)) _
    _ = _ := by ring

end NLS.LpSequence
