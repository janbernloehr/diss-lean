import NLS.ZakharovShabat.SourceMidpointTaylorLowerBound
import NLS.ZakharovShabat.SourceMidpointQuotientSup
import NLS.ZakharovShabat.SourceSquaredGapSharpness

/-!
# Stronger quotient summability would force stronger squared-gap summability

For real sources near zero, the positive neighboring Taylor term detects
each squared gap. At every exponent above both one and p/4, a stronger
quotient-supremum bound would transfer to the actual squared gaps. Finite
central indices are restored after testing the free centers on the tail.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}

theorem SourceIsolatingNeighborhoods.memℓp_squaredGap_of_midpointQuotientSup
    (h : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hq1 : 1 < q) (hq : q ≠ ⊤) (hquarter : p/4 ≤ q)
    (ψ : CoeffPair p) (hψ : ψ ∈ V)
    (hreal : IsRealType (CoeffPair.toMax p ψ))
    (hsmall : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ 1)
    (hsup : Memℓp (fun n : ℤ => (sourceMidpointQuotientSup hp hp1 D ψ n : ℂ)) q) :
    Memℓp (fun n : ℤ => (sourcePeriodicGapDisplacement hp hp1 ψ n)^2) q := by
  let : Fact (1 ≤ q) := ⟨hq1.le⟩
  let B : Coeff q := ⟨_,hsup⟩
  obtain ⟨S,hS,_⟩ := exists_sourceSquaredGapPhysicalRows hp hp1 ψ
  obtain ⟨E₀,_,hE⟩ := h.midpoint_taylor_majorant_of_row ψ hψ S (fun n => (hS n).2) le_rfl
  let E : Coeff q := ⟨fun n => E₀ n,(lp.memℓp E₀).of_exponent_ge hquarter⟩
  let C : ℝ := 8*(Real.pi+1)^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let a : ℤ → ℂ := fun n => (sourcePeriodicGapDisplacement hp hp1 ψ (n-1))^2
  obtain ⟨N,hN⟩ := h.tail
  have hpoint (n : ℤ) (hn : N+1 ≤ n.natAbs) :
      ‖a n‖ ≤ ‖((C : ℂ) • B) n‖+‖((C : ℂ) • E) n‖ := by
    have hz : (Real.pi : ℂ)*n ∈ D n := by
      rw [hN n (by omega)]
      exact mem_ball_self (by positivity : (0 : ℝ) < Real.pi/4)
    have hB : ‖sourceMidpointQuotient hp hp1 ψ n ((Real.pi : ℂ)*n)-1‖ ≤ ‖B n‖ := by
      apply (h.norm_le_midpointQuotientSup ψ hψ n _ hz).trans
      change sourceMidpointQuotientSup hp hp1 D ψ n ≤ ‖(sourceMidpointQuotientSup hp hp1 D ψ n : ℂ)‖
      simpa only [Complex.norm_real,Real.norm_eq_abs] using le_abs_self _
    have hlow := squared_sourceGap_le_neighbor_linearTerm hp hp1 ψ hreal hsmall (n-1)
    simp only [sub_add_cancel] at hlow
    have hlin : ‖sourceMidpointQuotientLinearTerm hp hp1 ψ n ((Real.pi : ℂ)*n)‖ ≤ ‖B n‖+‖E n‖ := by
      have he : sourceMidpointQuotientLinearTerm hp hp1 ψ n ((Real.pi : ℂ)*n) =
          (sourceMidpointQuotient hp hp1 ψ n ((Real.pi : ℂ)*n)-1)-
          (sourceMidpointQuotient hp hp1 ψ n ((Real.pi : ℂ)*n)-1-
            sourceMidpointQuotientLinearTerm hp hp1 ψ n ((Real.pi : ℂ)*n)) := by ring
      rw [he]
      exact (norm_sub_le _ _).trans (add_le_add hB (hE n _ hz))
    simp only [a,norm_pow,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,
      Complex.norm_real,Real.norm_of_nonneg hC]
    have hb := mul_le_mul_of_nonneg_left hlin hC
    dsimp only [C] at hb ⊢
    nlinarith
  obtain ⟨_,_,_,ha⟩ := Coeff.exists_tailCoeff_of_twoSequenceMajorants
    (zero_lt_one.trans hq1) hq1 hq le_rfl a (N+1) ((C : ℂ) • B) ((C : ℂ) • E) hpoint
  have hqr : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans hq1).ne' hq
  rw [memℓp_gen_iff hqr]
  have hs : Summable (fun n : ℤ =>
      ‖(sourcePeriodicGapDisplacement hp hp1 ψ ((n+1)-1))^2‖ ^ q.toReal) :=
    (Equiv.addRight (1 : ℤ)).summable_iff.mpr (ha.summable hqr)
  simpa only [add_sub_cancel_right] using hs

end NLS.ZakharovShabat
