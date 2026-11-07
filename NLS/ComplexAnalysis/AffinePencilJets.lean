import NLS.ComplexAnalysis.BanachFiniteJets

/-! # Analytic finite jets retain every domain requirement of an affine pencil -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
open NLS.FunctionalAnalysis
variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The derivative of a spectral increment times a Banach-valued analytic
function has precisely the expected shifted coefficient. -/
theorem iteratedDeriv_t_smul_succ {f : ℂ → D} (hf : AnalyticAt ℂ f 0) (k : ℕ) :
    iteratedDeriv (k+1) (fun t : ℂ => t • f t) 0 =
      (k+1:ℂ) • iteratedDeriv k f 0 := by
  have hid : ContDiffAt ℂ (k+1:ℕ) (fun t : ℂ => t) 0 := analyticAt_id.contDiffAt
  have hfk : ContDiffAt ℂ (k+1:ℕ) f 0 := hf.contDiffAt
  have he := iteratedDerivWithin_smul (𝕜 := ℂ) (𝔸 := ℂ) (n := k+1)
    (mem_univ (0:ℂ)) uniqueDiffOn_univ hid.contDiffWithinAt
      hfk.contDiffWithinAt
  simp only [iteratedDerivWithin_univ, Pi.smul_def'] at he
  rw [he, Finset.sum_eq_single 1]
  · rw [iteratedDeriv_fun_id_zero, if_pos rfl]
    simp only [Nat.choose_one_right, Nat.add_sub_cancel, one_smul]
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    simp
  · intro i _ hi
    rw [iteratedDeriv_fun_id_zero, if_neg hi]
    simp
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (by omega)))

/-- Factorial normalization makes multiplication by the increment a pure shift. -/
theorem normalized_iteratedDeriv_t_smul_succ {f : ℂ → D} (hf : AnalyticAt ℂ f 0) (k : ℕ) :
    (((k+1).factorial:ℂ)⁻¹) • iteratedDeriv (k+1) (fun t : ℂ => t • f t) 0 =
      ((k.factorial:ℂ)⁻¹) • iteratedDeriv k f 0 := by
  rw [iteratedDeriv_t_smul_succ hf, smul_smul]
  have hc : ((k+1).factorial:ℂ) = (k+1:ℂ)*(k.factorial:ℂ) := by
    exact_mod_cast Nat.factorial_succ k
  have hk : (k.factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk1 : (k+1:ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hs : (((k+1).factorial:ℂ)⁻¹)*(k+1:ℂ) = (k.factorial:ℂ)⁻¹ := by
    rw [hc]
    field_simp
  rw [hs]

/-- If the retained derivatives of an affine pencil vanish, the actual
Banach-domain Taylor coefficients form a domain-preserving finite root chain. -/
theorem analyticFiniteJet_mem_pencilChainSpace (J P : D →L[ℂ] E)
    {f : ℂ → D} (hf : AnalyticAt ℂ f 0) (N : ℕ)
    (hR : ∀ k : Fin N, iteratedDeriv k.val (fun t : ℂ => t • J (f t)-P (f t)) 0 = 0) :
    analyticFiniteJet N f ∈ pencilChainSpace J.toLinearMap P.toLinearMap N := by
  have hJ : AnalyticAt ℂ (fun t => J (f t)) 0 := (J.analyticAt _).comp (f := f) hf
  have hP : AnalyticAt ℂ (fun t => P (f t)) 0 := (P.analyticAt _).comp (f := f) hf
  have ht : AnalyticAt ℂ (fun t : ℂ => t • J (f t)) 0 := analyticAt_id.smul hJ
  induction N with
  | zero => exact Submodule.mem_top
  | succ N ih =>
    rw [mem_pencilChainSpace_succ]
    refine ⟨ih (fun k => hR k.castSucc), ?_⟩
    cases N with
    | zero =>
      have he := hR (Fin.last 0)
      have he' : -P (f 0) = 0 := by
        simpa only [Fin.val_last, iteratedDeriv_zero, zero_smul, zero_sub] using he
      simpa [analyticFiniteJet, iteratedDeriv_zero] using (neg_eq_zero.mp he')
    | succ m =>
      change P (analyticFiniteJet (m+2) f (Fin.last (m+1))) =
        J (analyticFiniteJet (m+1) f (Fin.last m))
      have hz : analyticFiniteJet (m+2) (fun t : ℂ => t • J (f t)-P (f t))
          (Fin.last (m+1)) = 0 := by
        change (((m+1).factorial:ℂ)⁻¹) • iteratedDeriv (m+1)
          (fun t : ℂ => t • J (f t)-P (f t)) 0 = 0
        have he := hR (Fin.last (m+1))
        change iteratedDeriv (m+1) (fun t : ℂ => t • J (f t)-P (f t)) 0 = 0 at he
        rw [he, smul_zero]
      rw [analyticFiniteJet_sub ht hP, analyticFiniteJet_compCLM P hf] at hz
      have hm : analyticFiniteJet (m+2) (fun t : ℂ => t • J (f t)) (Fin.last (m+1)) =
          J (analyticFiniteJet (m+1) f (Fin.last m)) := by
        change (((m+1).factorial:ℂ)⁻¹) • iteratedDeriv (m+1) (fun t : ℂ => t • J (f t)) 0 = _
        rw [normalized_iteratedDeriv_t_smul_succ hJ]
        exact congrFun (analyticFiniteJet_compCLM J hf (m+1)) (Fin.last m)
      change analyticFiniteJet (m+2) (fun t : ℂ => t • J (f t)) (Fin.last (m+1)) -
        P (analyticFiniteJet (m+2) f (Fin.last (m+1))) = 0 at hz
      rw [hm] at hz
      exact (sub_eq_zero.mp hz).symm

/-- Centering an analytic scalar function preserves its actual vanishing order. -/
theorem analyticOrderAt_const_add_zero {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    analyticOrderAt (fun t : ℂ => f (z+t)) 0 = analyticOrderAt f z := by
  have h0 : AnalyticAt ℂ f (z+(0:ℂ)) := by simpa only [add_zero] using hf
  have hh : AnalyticAt ℂ (fun t : ℂ => f (z+t)) 0 :=
    h0.comp (f := fun t : ℂ => z+t) (analyticAt_const.add analyticAt_id)
  apply ENat.eq_of_forall_natCast_le_iff
  intro k
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hh,
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
  simp only [iteratedDeriv_comp_const_add, add_zero]

end NLS.ComplexAnalysis
