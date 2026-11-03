import NLS.SequenceSpaces.PositiveIndexPowerWeight
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Basic

/-! # Analytic l2 realization of twice-weighted inverse column errors -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.Coeff
variable {E : Type*}

def twoWeightedInverseError
    (Q : E → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n : ℕ+) (q : E) : NLS.Coeff 2 :=
  (n : ℂ)^2 • (Q q (lp.single 2 (n : ℤ) 1)-lp.single 2 (n : ℤ) 1)

theorem twoWeightedInverseError_apply
    (R Q : E → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : E)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q q (lp.single 2 j 1)) m)
    (n : ℕ+) (m : ℤ) :
    twoWeightedInverseError Q n q m =
      NLS.Coeff.positiveIndexWeight m^2*
        ((R q (lp.single 2 (n : ℤ) 1)) m-(lp.single 2 (n : ℤ) (1 : ℂ) : NLS.Coeff 2) m) := by
  have hn : (0 : ℤ) < n := by exact_mod_cast n.pos
  have he := hcompat m (n : ℤ)
  have hwn : NLS.Coeff.positiveIndexWeight (n : ℤ) = (n : ℂ) := by
    simp only [NLS.Coeff.positiveIndexWeight,if_pos hn,Int.cast_natCast]
  rw [hwn] at he
  change (n : ℂ)^2*((Q q (lp.single 2 (n : ℤ) 1)) m-
    (lp.single 2 (n : ℤ) (1 : ℂ) : NLS.Coeff 2) m) = _
  rw [mul_sub,mul_sub,← he]
  by_cases hmn : m = (n : ℤ)
  · subst m
    simp only [NLS.Coeff.positiveIndexWeight,if_pos hn,Int.cast_natCast]
  · simp only [lp.single_apply,Pi.single_apply,if_neg hmn,mul_zero,sub_zero]

theorem twoWeightedInverseError_memlp
    (R Q : E → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : E)
    (hcompat : ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q q (lp.single 2 j 1)) m) (n : ℕ+) :
    Memℓp (fun m : ℤ => NLS.Coeff.positiveIndexWeight m^2*
      ((R q (lp.single 2 (n : ℤ) 1)) m-(lp.single 2 (n : ℤ) (1 : ℂ) : NLS.Coeff 2) m)) 2 := by
  have he : (fun m : ℤ => NLS.Coeff.positiveIndexWeight m^2*
      ((R q (lp.single 2 (n : ℤ) 1)) m-(lp.single 2 (n : ℤ) (1 : ℂ) : NLS.Coeff 2) m)) =
      (fun m => twoWeightedInverseError Q n q m) :=
    funext (fun m => (twoWeightedInverseError_apply R Q q hcompat n m).symm)
  rw [he]
  exact lp.memℓp (twoWeightedInverseError Q n q)

section analytic
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem twoWeightedInverseError_analytic
    (Q : E → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (V : Set (E)) (hQa : AnalyticOnNhd ℂ Q V) (n : ℕ+) :
    AnalyticOnNhd ℂ (twoWeightedInverseError Q n) V := by
  intro q hq
  have hc : AnalyticAt ℂ (fun x : E => Q x (lp.single 2 (n : ℤ) 1)) q := by
    simpa only [Function.comp_def] using!
      ((ContinuousLinearMap.apply ℂ (NLS.Coeff 2) (lp.single 2 (n : ℤ) 1)).analyticAt (Q q)).comp
        (f := Q) (hQa q hq)
  exact (analyticAt_const (v := (n : ℂ)^2)).smul
    (hc.sub (analyticAt_const (v := (lp.single 2 (n : ℤ) 1 : NLS.Coeff 2))))

omit [NormedSpace ℂ E] in
theorem twoWeightedInverseError_free
    (Q : E → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hQ0 : Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) (n : ℕ+) :
    twoWeightedInverseError Q n 0 = 0 := by
  simp only [twoWeightedInverseError,hQ0,ContinuousLinearMap.id_apply,sub_self,smul_zero]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem norm_twoWeightedInverseError_le
    (Q : E → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (n : ℕ+) (q : E) :
    ‖twoWeightedInverseError Q n q‖ ≤
      (n : ℝ)^2*‖Q q-ContinuousLinearMap.id ℂ (NLS.Coeff 2)‖ := by
  have he : twoWeightedInverseError Q n q =
      (n : ℂ)^2 • ((Q q-ContinuousLinearMap.id ℂ (NLS.Coeff 2)) (lp.single 2 (n : ℤ) 1)) := rfl
  rw [he,norm_smul,norm_pow,Complex.norm_natCast]
  have hen : ‖(lp.single 2 (n : ℤ) (1 : ℂ) : NLS.Coeff 2)‖ = 1 := by
    rw [lp.norm_single (by norm_num),norm_one]
  simpa only [hen,mul_one] using
    mul_le_mul_of_nonneg_left ((Q q-ContinuousLinearMap.id ℂ (NLS.Coeff 2)).le_opNorm
      (lp.single 2 (n : ℤ) 1)) (sq_nonneg (n : ℝ))

/-- A single neighborhood controls every weighted column error, with its
exact n^2 scaling. No mode-dependent neighborhood is selected. -/
theorem exists_uniform_small_twoWeightedInverseError
    (Q : E → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (V : Set (E)) (hV : IsOpen V) (h0V : 0 ∈ V)
    (hQa : AnalyticOnNhd ℂ Q V) (hQ0 : Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set (E), U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧
      ∀ q ∈ U, ∀ n : ℕ+, ‖twoWeightedInverseError Q n q‖ ≤ ε*(n : ℝ)^2 := by
  have hc := ((hQa 0 h0V).sub (analyticAt_const (v := ContinuousLinearMap.id ℂ (NLS.Coeff 2)))).continuousAt.norm
  have hs : ∀ᶠ q in 𝓝 (0 : E),
      ‖Q q-ContinuousLinearMap.id ℂ (NLS.Coeff 2)‖ < ε :=
    hc.eventually (gt_mem_nhds (by
      change ‖Q 0-ContinuousLinearMap.id ℂ (NLS.Coeff 2)‖ < ε
      simpa only [hQ0,sub_self,norm_zero] using hε))
  obtain ⟨B,hBsub,hB,h0B⟩ := _root_.mem_nhds_iff.mp hs
  refine ⟨V ∩ B,inter_subset_left,hV.inter hB,⟨h0V,h0B⟩,?_⟩
  intro q hq n
  exact (norm_twoWeightedInverseError_le Q n q).trans
    (by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (hBsub hq.2).le (sq_nonneg (n : ℝ)))

end analytic
end NLS.Coeff
