import NLS.SequenceSpaces.UniformHolderSums

/-! Squared full-l2 gaps and the two signed reciprocal factors give
absolute convergence of the gap-index-weighted moment in each row.
Finitely many low terms and the diagonal are unrestricted. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal Classical
namespace NLS.Coeff

theorem summable_norm_positive_weighted_of_squared_gap_tail
    (a : Coeff 2) (n : ℕ+) (u : ℕ+ → ℂ) (K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ m : ℕ+, K < (m:ℕ) → m ≠ n → ‖u m‖ ≤
      C*‖a ((m:ℕ):ℤ)‖^2*
        (1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))) :
    Summable (fun m : ℕ+ => ‖((m:ℕ):ℂ)*u m‖) := by
  have hc : (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal := Real.HolderConjugate.two_two
  have hsZ : Summable (fun k : ℤ => ‖a k‖^2) := by
    simpa only [pow_two] using (lp.tsum_mul_le_mul_norm hc a a).1
  have hinj : Function.Injective (fun m : ℕ+ => ((m:ℕ):ℤ)) := by
    intro i j h
    apply PNat.coe_injective
    exact Int.ofNat.inj h
  have hs := (hsZ.comp_injective hinj).mul_left (3*C)
  let L := max K (2*(n:ℕ))
  let v : ℕ+ → ℂ := fun m => if L < (m:ℕ) then ((m:ℕ):ℂ)*u m else 0
  have hv : Summable (fun m => ‖v m‖) := by
    apply hs.of_nonneg_of_le (fun _ => norm_nonneg _) _
    intro m
    change ‖v m‖ ≤ (3*C)*‖a ((m:ℕ):ℤ)‖^2
    by_cases hm : L < (m:ℕ)
    · have hmK : K < (m:ℕ) := (le_max_left _ _).trans_lt hm
      have hm2 : 2*(n:ℕ) < (m:ℕ) := (le_max_right _ _).trans_lt hm
      have hmn : m ≠ n := by intro he; subst m; have := n.pos; omega
      have hnr : 0 < ((n:ℕ):ℝ) := by exact_mod_cast n.pos
      have hmr : 2*((n:ℕ):ℝ) < ((m:ℕ):ℝ) := by exact_mod_cast hm2
      have hker : ((m:ℕ):ℝ)*(1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)) ≤ 3 := by
        rw [abs_of_neg (by linarith : ((n:ℕ):ℝ)-(m:ℕ)<0),neg_sub,mul_add,
          mul_one_div,mul_one_div]
        have h₁ : ((m:ℕ):ℝ)/(((m:ℕ):ℝ)-(n:ℕ)) ≤ 2 :=
          (div_le_iff₀ (by linarith)).mpr (by linarith)
        have h₂ : ((m:ℕ):ℝ)/(((n:ℕ):ℝ)+(m:ℕ)) ≤ 1 :=
          (div_le_iff₀ (by linarith)).mpr (by linarith)
        linarith
      rw [show v m=((m:ℕ):ℂ)*u m from if_pos hm,norm_mul,Complex.norm_natCast]
      calc
        _ ≤ ((m:ℕ):ℝ)*(C*‖a ((m:ℕ):ℤ)‖^2*
            (1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))) :=
          mul_le_mul_of_nonneg_left (hu m hmK hmn) (by positivity)
        _ = (C*‖a ((m:ℕ):ℤ)‖^2)*
            (((m:ℕ):ℝ)*(1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))) := by ring
        _ ≤ (C*‖a ((m:ℕ):ℤ)‖^2)*3 := mul_le_mul_of_nonneg_left hker (by positivity)
        _ = _ := by ring
    · simp only [v,if_neg hm,norm_zero]
      positivity
  have hfinite : {m : ℕ+ | (m:ℕ) ≤ L}.Finite :=
    (Set.finite_Iic L).preimage (fun _ _ _ _ h => PNat.coe_injective h)
  apply hv.congr_cofinite
  filter_upwards [hfinite.compl_mem_cofinite] with m hm
  have hmL : L < (m:ℕ) := lt_of_not_ge hm
  simp only [v,if_pos hmL]

end NLS.Coeff
