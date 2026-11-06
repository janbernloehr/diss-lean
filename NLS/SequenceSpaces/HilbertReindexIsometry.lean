import NLS.SequenceSpaces.Basic

/-! # Exact Hilbert reindexing for arbitrary index equivalences -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.SequenceSpaces
variable {ι κ : Type*}

theorem memlp_hilbert_reindex (e : ι ≃ κ) (b : lp (fun _ : ι => ℂ) 2) :
    Memℓp (fun n : κ => b (e.symm n)) 2 := by
  apply memℓp_gen
  exact e.symm.summable_iff.mpr
    ((lp.memℓp b).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal))

def hilbertReindex (e : ι ≃ κ) (b : lp (fun _ : ι => ℂ) 2) : lp (fun _ : κ => ℂ) 2 :=
  ⟨fun n => b (e.symm n),memlp_hilbert_reindex e b⟩

theorem norm_hilbertReindex (e : ι ≃ κ) (b : lp (fun _ : ι => ℂ) 2) : ‖hilbertReindex e b‖ = ‖b‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  congr 1
  exact e.symm.tsum_eq (fun k : ι => ‖b k‖^(2 : ℝ≥0∞).toReal)

def hilbertReindexIsometry (e : ι ≃ κ) : lp (fun _ : ι => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : κ => ℂ) 2 where
  toFun := hilbertReindex e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := norm_hilbertReindex e

end NLS.SequenceSpaces
