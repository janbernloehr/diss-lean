import NLS.ZakharovShabat.SourcePsiCriticalResidueBounds
import NLS.SequenceSpaces.ConjugateDuality

/-! # Absolutely convergent actual critical interpolation

The reciprocal critical kernel is a genuine Hilbert sequence at every
fixed evaluation point. Holder pairing with the proved actual residue
sequence turns the symmetric Cauchy limits into ordinary absolute sums.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem memℓp_canonicalCriticalReciprocal_two
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (w : ℂ) :
    Memℓp (fun m : ℤ => (w-canonicalCriticalPoints hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) m)⁻¹) 2 := by
  let β := canonicalCriticalPoints hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
  let b := canonicalCriticalDisplacement hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)
  let f : ℤ → ℂ := fun m => (w-β m)⁻¹
  obtain ⟨M,hM⟩ := exists_nat_gt (2*(‖w‖+‖b‖)/Real.pi)
  let S := Finset.Icc (-(M:ℤ)) M
  apply (Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_head_tail_bound (p := 2)
    f f S (Coeff.puncturedLattice 2 (by norm_num)) 0 (2/Real.pi) (by positivity)
    (fun _ _ => le_rfl) ?_).1
  intro m hm
  have hMm : M < m.natAbs := by dsimp only [S] at hm; simp only [Finset.mem_Icc] at hm; omega
  have hm0 : m ≠ 0 := by intro h; simp only [h,Int.natAbs_zero] at hMm; omega
  have hmp : 0 < (m.natAbs:ℝ) := by exact_mod_cast (show 0 < m.natAbs by omega)
  have hMreal : 2*(‖w‖+‖b‖) < (M:ℝ)*Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp (by exact_mod_cast hM)
  have hlarge : 2*(‖w‖+‖b‖) < Real.pi*(m.natAbs:ℝ) := by
    have ht : (M:ℝ) < (m.natAbs:ℝ) := by exact_mod_cast hMm
    nlinarith [Real.pi_pos]
  have hb : ‖b m‖ ≤ ‖b‖ := lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' b m
  have he : β m-b m = (Real.pi:ℂ)*m := by simp only [b,β,canonicalCriticalDisplacement_apply]; ring
  have hlow := norm_sub_le (β m) (b m)
  rw [he] at hlow
  have hcenter : ‖(Real.pi:ℂ)*m‖ = Real.pi*(m.natAbs:ℝ) := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
      Complex.norm_intCast,Nat.cast_natAbs,Int.cast_abs]
  rw [hcenter] at hlow
  have hup := norm_le_norm_sub_add (β m) w
  rw [norm_sub_rev (β m) w] at hup
  have hhalf : Real.pi*(m.natAbs:ℝ)/2 ≤ ‖w-β m‖ := by linarith
  have hden : 0 < ‖w-β m‖ := (half_pos (mul_pos Real.pi_pos hmp)).trans_le hhalf
  have hbound : ‖f m‖ ≤ (2/Real.pi)/(m.natAbs:ℝ) := by
    change ‖(w-β m)⁻¹‖ ≤ _
    rw [norm_inv,inv_eq_one_div]
    apply (div_le_div_iff₀ hden hmp).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ Real.pi_pos).mpr
    nlinarith
  simpa only [Coeff.puncturedLattice_apply,if_neg hm0,norm_inv,Complex.norm_intCast,
    lp.coeFn_zero,Pi.zero_apply,norm_zero,add_zero,div_eq_mul_inv,Nat.cast_natAbs,Int.cast_abs] using hbound

theorem summable_norm_sourcePsiCriticalInterpolation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : CoeffPair p)
    (hr : IsRealType (CoeffPair.toMax p φ)) (w : ℂ) :
    Summable (fun m : ℤ => ‖sourcePsiCriticalInterpolationTerm hp hp1 n a φ m w‖) := by
  let r : Coeff 2 := ⟨sourcePsiCriticalResidue hp hp1 n a φ,memℓp_sourcePsiCriticalResidue_two hp hp1 n a φ hr⟩
  let k : Coeff 2 := ⟨fun m => (w-canonicalCriticalPoints hp hp1
    (periodOnePotential φ) (periodOnePotential_mem φ) m)⁻¹,memℓp_canonicalCriticalReciprocal_two hp hp1 φ w⟩
  have h := Coeff.summable_norm_dualPairing r k
  simpa only [sourcePsiCriticalInterpolationTerm,div_eq_mul_inv] using! h

theorem sourcePsiCriticalInterpolation_tsum_eq_quotient
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (φ : CoeffPair p)
    (hr : IsRealType (CoeffPair.toMax p φ)) (w : ℂ)
    (hw : deriv (canonicalDiscriminant hp (periodOnePotential φ)) w ≠ 0) :
    (∑' m : ℤ, sourcePsiCriticalInterpolationTerm hp hp1 n a φ m w) =
      sourcePsiCandidate n (w,a)/deriv (canonicalDiscriminant hp (periodOnePotential φ)) w := by
  have hs := (summable_norm_sourcePsiCriticalInterpolation hp hp1 n a φ hr w).of_norm.hasSum.comp
    Finset.tendsto_Icc_neg
  have ht := (tendstoUniformlyOn_sourcePsiCriticalInterpolation hp hp1 n a φ hr ‖w‖ (norm_nonneg w)).tendsto_at
    (show w ∈ {w | ‖w‖ ≤ ‖w‖ ∧ deriv (canonicalDiscriminant hp (periodOnePotential φ)) w ≠ 0} from ⟨le_rfl,hw⟩)
  exact tendsto_nhds_unique (by simpa only [Function.comp_def] using hs) ht

end NLS.ZakharovShabat
