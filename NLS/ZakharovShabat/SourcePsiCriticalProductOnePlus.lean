import NLS.ZakharovShabat.SourcePsiCriticalSummableDifference
import NLS.ZakharovShabat.SourceCriticalRelativeRowBound
import NLS.ZakharovShabat.SourceCriticalRootRatioUniformTailBound

/-! # Every-exponent gap majorants for the actual deleted-product difference

The summable actual root difference supplies every reciprocal-row exponent.
The existing product comparison uses its full displacement norm only in a
uniform exponential constant. Thus one source neighborhood, chosen before
the target exponent, controls every deleted index simultaneously.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual psi/critical deleted-product difference has an ℓq gap majorant
for every finite q>1, uniformly in the deleted index on one source neighborhood. -/
theorem SourceLemma12_11Data.exists_local_critical_product_onePlus_majorants
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (hp2 : 2 < p)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ.val ∈ V ∧ V ⊆ W ∧ ∃ K : ℕ,
      ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 ≤ M ∧
        ∀ ψ ∈ V, ∀ n : ℤ, ∃ B : Coeff q, ‖B‖ ≤ M ∧ ∀ k : ℤ, K ≤ k.natAbs →
          ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
            ‖sourcePsiCriticalFilledQuotient hp hp1 n k (s n ψ) ψ z-
              sourceCriticalDeletedQuotient hp hp1 k ψ z‖ ≤ ‖B k‖ := by
  obtain ⟨Vr,hVr,hφr,hVrW,hrows⟩ := H.exists_local_critical_difference_reciprocal_rows hp2 φ hφ
  obtain ⟨Vl,hVl,hφl,_,L,hL,hl⟩ := H.exists_local_uniform_critical_filled_difference_norm_bound φ hφ
  obtain ⟨Vm,hVm,hφm,Km,M,hM,hm⟩ :=
    exists_local_uniform_sourceCriticalRootRatioExtension_tail_bound hp hp1 φ.val φ.property
  obtain ⟨Vq,hVq,hφq,_,Kq,hq⟩ := H.exists_local_critical_filled_quotient_small_tail φ hφ 1 (by norm_num)
  obtain ⟨I,_,_,hrealI,hisol⟩ := sourceLemma10_1 hp hp1
  obtain ⟨Vd,hVd,_,hφd,_,χ,_,N,ε,_,_,c,hD⟩ := hisol φ.val (hrealI φ.property)
  let V := ((Vr ∩ Vl) ∩ (Vm ∩ Vq)) ∩ Vd
  let κ := ‖Coeff.puncturedLattice p.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖
  let J := M*Real.exp (c*L*κ)*c
  have hc : 0 < c := zero_lt_one.trans_le hD.one_le
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  refine ⟨V,((hVr.inter hVl).inter (hVm.inter hVq)).inter hVd,
    ⟨⟨⟨hφr,hφl⟩,hφm,hφq⟩,hφd⟩,fun _ h => hVrW h.1.1.1,max Km Kq,?_⟩
  intro q hqtop hq1
  let : Fact (1 ≤ q) := ⟨hq1.le⟩
  obtain ⟨R,hR,hr⟩ := hrows q hqtop hq1
  refine ⟨J*R,mul_nonneg hJ hR,?_⟩
  intro ψ hψ n
  obtain ⟨B,hB,hBrow⟩ := hr ψ hψ.1.1.1 n
  let E := (J:ℂ) • Coeff.magnitude B
  have hE (k : ℤ) : ‖E k‖ = J*‖B k‖ := by
    simp only [E,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg hJ,Coeff.magnitude_apply,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
  refine ⟨E,?_,?_⟩
  · calc
      ‖E‖ = J*‖B‖ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hJ,Coeff.norm_magnitude]
      _ ≤ J*R := mul_le_mul_of_nonneg_left hB hJ
  · intro k hk z hz
    have hkm : Km ≤ k.natAbs := (le_max_left _ _).trans hk
    have hkq : Kq ≤ k.natAbs := (le_max_right _ _).trans hk
    have hzq : z ∈ ball ((Real.pi:ℂ)*k) (Real.pi/4) :=
      ball_subset_ball (by linarith [Real.pi_pos]) ((hq ψ hψ.1.2.2 n k hkq).1 hz)
    have hχ : ‖sourceCriticalDeletedQuotient hp hp1 k ψ z‖ ≤ M := by
      simpa only [sourceCriticalRootRatioExtension,norm_mul,norm_neg,norm_I,one_mul,
        sourceCriticalDeletedQuotient] using hm ψ hψ.1.2.1 k hkm z hzq
    rw [hE,hBrow]
    exact hD.norm_quotient_sub_critical_le_reciprocalRow ψ hψ.2 k
      (sourcePsiFillDeletedRoot n (s n ψ) (sourceCriticalRoot hp hp1 ψ n)) z
      (subset_closure (hD.gap ψ hψ.2 k hz)) M L hχ (hl ψ hψ.1.1.2 n)

end NLS.ZakharovShabat
