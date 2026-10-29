import NLS.ZakharovShabat.SourceStandardRootSqrtRemainder
import NLS.ZakharovShabat.SourceStandardRootAnalytic
import NLS.SequenceSpaces.QuasiHolderProduct
import NLS.SequenceSpaces.Reflection

/-!
# Refined coefficients in the paired standard-root errors

The proof of Lemma 10.5 retains an actual quadratic remainder in ℓ^(p/2),
not only a scalar O(k⁻²) estimate. Its product with its reflected sequence
belongs to ℓ^(p/4), including exponents below one. The identities below
keep the actual midpoint and gap data and a uniform large-index cutoff.
-/

noncomputable section
open Set Complex Filter
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The coefficient of the literal quadratic denominator in the root-factor remainder. -/
def sourceStandardRootQuadraticRemainder (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) (k : ℤ) : ℂ :=
  (k : ℂ)^2 * sourceStandardRootSqrtCorrection hp hp1 ψ z k

/-- Retaining each actual gap, rather than its sequence supremum, gives the half-exponent bound. -/
theorem norm_sourceStandardRootQuadraticRemainder_tail_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) (k : ℤ)
    (hk : k ≠ 0)
    (hlarge : 2*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖+‖z‖) ≤
      Real.pi*|(k : ℝ)|) :
    ‖sourceStandardRootQuadraticRemainder hp hp1 ψ z k‖ ≤
      (1/(2*Real.pi^2))*‖(canonicalPeriodicGap hp hp1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) k)^2‖ := by
  let t := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k
  let g := canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k
  let d : ℂ := (Real.pi : ℂ)*k
  have hd : d ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast hk)
  have hdn : ‖d‖ = Real.pi*|(k : ℝ)| := by
    simp [d, Complex.norm_intCast, abs_of_pos Real.pi_pos]
  have ht : ‖t-d‖ ≤ ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ := by
    simpa only [sourcePeriodicMidpointDisplacement_apply] using
      lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
        (sourcePeriodicMidpointDisplacement hp hp1 ψ) k
  have hsep : ‖d‖ ≤ 2*‖t-z‖ :=
    free_midpoint_separation t d z (by rw [hdn]; linarith)
  have hb := norm_standardRootSqrtCorrection_le_quadratic t (g^2) d z hd hsep
  have hkR : |(k : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hk)
  simp only [sourceStandardRootQuadraticRemainder,sourceStandardRootSqrtCorrection,if_neg hk,
    norm_mul,norm_pow,Complex.norm_intCast]
  change |(k : ℝ)|^2*‖standardRootSqrtCorrection t (g^2) d z‖ ≤ _
  calc
    _ ≤ |(k : ℝ)|^2*(‖g^2‖/(2*‖d‖^2)) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = (1/(2*Real.pi^2))*‖g^2‖ := by
      rw [hdn]
      field_simp
    _ = (1/(2*Real.pi^2))*‖g‖^2 := by rw [norm_pow]

/-- The exact quadratic remainder coefficient belongs to the literal half exponent, even below one. -/
theorem memℓp_sourceStandardRootQuadraticRemainder
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) :
    Memℓp (sourceStandardRootQuadraticRemainder hp hp1 ψ z) (p/2) := by
  let F := sourceStandardRootQuadraticRemainder hp hp1 ψ z
  obtain ⟨N,hN⟩ := exists_nat_gt
    (2*(‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖+‖z‖)/Real.pi)
  let H : ℤ → ℂ := fun k => if N < k.natAbs then 0 else F k
  let T : ℤ → ℂ := fun k => if N < k.natAbs then F k else 0
  have hH : Memℓp H (p/2) := by
    apply Memℓp.of_exponent_ge (p := p/2) (q := 0) ?_ bot_le
    apply memℓp_zero
    apply (Finset.Icc (-(N : ℤ)) N).finite_toSet.subset
    intro k hk
    have hle : k.natAbs ≤ N := by
      by_contra hn
      exact hk (by simp [H,lt_of_not_ge hn])
    simp only [Finset.mem_coe,Finset.mem_Icc]
    omega
  have hT : Memℓp T (p/2) := by
    apply ((memℓp_sourcePeriodicSquaredGap hp hp1 ψ).norm.const_mul
      (1/(2*Real.pi^2))).mono
    intro k
    by_cases hk : N < k.natAbs
    · simp only [T,if_pos hk]
      apply norm_sourceStandardRootQuadraticRemainder_tail_le hp hp1 ψ z k (by omega)
      have hkr : (N : ℝ) < (k.natAbs : ℝ) := by exact_mod_cast hk
      have habs : |(k : ℝ)| = (k.natAbs : ℝ) := by simp
      rw [habs]
      have hlt := (div_lt_iff₀ Real.pi_pos).mp (hN.trans hkr)
      linarith
    · simp only [T,if_neg hk,norm_zero]
      positivity
  have heq : F = H+T := by
    funext k
    dsimp [H,T]
    split <;> simp
  rw [show sourceStandardRootQuadraticRemainder hp hp1 ψ z = F from rfl,heq]
  exact hH.add hT

/-- The three-term factor expansion with its actual half-exponent remainder. -/
theorem sourceStandardRootRelativeError_eq_quadraticRemainder
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) (k : ℤ) (hk : k ≠ 0) :
    sourceStandardRootRelativeError hp hp1 ψ k z =
      sourcePeriodicMidpointDisplacement hp hp1 ψ k/((Real.pi : ℂ)*k)-
        z/((Real.pi : ℂ)*k)+sourceStandardRootQuadraticRemainder hp hp1 ψ z k/(k : ℂ)^2 := by
  rw [sourceStandardRootRelativeError_eq hp hp1 ψ k z hk]
  simp only [sourceStandardRootQuadraticRemainder,sourceStandardRootSqrtCorrection,if_neg hk]
  have hkC : (k : ℂ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hk)
  rw [mul_div_cancel_left₀ _ hkC]
  rfl

omit [Fact (1 ≤ p)] in
private theorem source_half_exponent_pos (hp : p ≠ ⊤) (hp1 : 1 < p) :
    0 < (p/2).toReal := by
  have h := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  rw [ENNReal.toReal_div]
  norm_num
  positivity

private def reflectedQuadraticRemainder (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) : Coeff (p/2) :=
  ⟨fun k => sourceStandardRootQuadraticRemainder hp hp1 ψ z (-k),by
    change Memℓp (fun k : ℤ => sourceStandardRootQuadraticRemainder hp hp1 ψ z (-k)) (p/2)
    have hs : Summable (fun k : ℤ => ‖sourceStandardRootQuadraticRemainder hp hp1 ψ z k‖^(p/2).toReal) :=
      (memℓp_sourceStandardRootQuadraticRemainder hp hp1 ψ z).summable
        (source_half_exponent_pos hp hp1)
    exact memℓp_gen (hs.comp_injective (neg_injective : Function.Injective (fun k : ℤ => -k)))⟩

/-- The paired linear error has the literal lp/k plus l(p/2)/k^2 decomposition. -/
theorem exists_sourceStandardRoot_paired_error_coefficients
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) :
    ∃ L : Coeff p, ∃ R : Coeff (p/2), ∀ k : ℤ, k ≠ 0 →
      sourceStandardRootRelativeError hp hp1 ψ k z+
        sourceStandardRootRelativeError hp hp1 ψ (-k) z =
      L k/(k : ℂ)+R k/(k : ℂ)^2 := by
  let d := sourcePeriodicMidpointDisplacement hp hp1 ψ
  let Q : Coeff (p/2) := ⟨sourceStandardRootQuadraticRemainder hp hp1 ψ z,
    memℓp_sourceStandardRootQuadraticRemainder hp hp1 ψ z⟩
  let Qn := reflectedQuadraticRemainder hp hp1 ψ z
  refine ⟨(Real.pi : ℂ)⁻¹ • (d-Coeff.reflection d),Q+Qn,?_⟩
  intro k hk
  rw [sourceStandardRootRelativeError_eq_quadraticRemainder hp hp1 ψ z k hk,
    sourceStandardRootRelativeError_eq_quadraticRemainder hp hp1 ψ z (-k) (neg_ne_zero.mpr hk)]
  simp only [lp.coeFn_smul,lp.coeFn_sub,lp.coeFn_add,Pi.smul_apply,Pi.sub_apply,
    Pi.add_apply,smul_eq_mul,Coeff.reflection_apply,Int.cast_neg]
  change _ = (Real.pi : ℂ)⁻¹*(d k-d (-k))/(k : ℂ)+
    (sourceStandardRootQuadraticRemainder hp hp1 ψ z k+
      sourceStandardRootQuadraticRemainder hp hp1 ψ z (-k))/(k : ℂ)^2
  dsimp [d]
  ring

private def sourceRootLinearFactorCoeff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) : Coeff ⊤ :=
  ⟨fun k => (sourcePeriodicMidpointDisplacement hp hp1 ψ k-z)/(Real.pi : ℂ),by
    change Memℓp (fun k : ℤ => (sourcePeriodicMidpointDisplacement hp hp1 ψ k-z)/(Real.pi : ℂ)) ⊤
    apply memℓp_infty
    refine ⟨(‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖+‖z‖)/Real.pi,?_⟩
    rintro v ⟨k,rfl⟩
    dsimp only
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    apply div_le_div_of_nonneg_right _ Real.pi_pos.le
    apply (norm_sub_le _ _).trans
    gcongr
    exact lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      (sourcePeriodicMidpointDisplacement hp hp1 ψ) k⟩

/-- The quadratic cross term has exactly the bounded/k^2, l(p/2)/k^3 and l(p/4)/k^4 form. -/
theorem exists_sourceStandardRoot_cross_error_coefficients
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) :
    ∃ A : Coeff ⊤, ∃ B : Coeff (p/2), ∃ C : Coeff (p/4), ∀ k : ℤ, k ≠ 0 →
      sourceStandardRootRelativeError hp hp1 ψ k z*
        sourceStandardRootRelativeError hp hp1 ψ (-k) z =
      A k/(k : ℂ)^2+B k/(k : ℂ)^3+C k/(k : ℂ)^4 := by
  let b := sourceRootLinearFactorCoeff hp hp1 ψ z
  let bn := Coeff.reflection b
  let Q : Coeff (p/2) := ⟨sourceStandardRootQuadraticRemainder hp hp1 ψ z,
    memℓp_sourceStandardRootQuadraticRemainder hp hp1 ψ z⟩
  let Qn := reflectedQuadraticRemainder hp hp1 ψ z
  let A := -(Coeff.quasiHolderProduct (r := ⊤) b bn)
  let B := Coeff.quasiHolderProduct (r := p/2) b Qn-
    Coeff.quasiHolderProduct (r := p/2) bn Q
  let : (p/2).HolderTriple (p/2) (p/2/2) := Coeff.holderTriple_half (p/2)
  have hq : p/2/2 = p/4 := by
    simp only [div_eq_mul_inv,mul_assoc]
    congr 1
    rw [← ENNReal.mul_inv (a := 2) (b := 2) (by simp) (by simp)]
    norm_num
  let C₀ := Coeff.quasiHolderProduct (r := p/2/2) Q Qn
  let C : Coeff (p/4) := ⟨fun k => C₀ k,by rw [← hq]; exact lp.memℓp C₀⟩
  refine ⟨A,B,C,?_⟩
  intro k hk
  rw [sourceStandardRootRelativeError_eq_quadraticRemainder hp hp1 ψ z k hk,
    sourceStandardRootRelativeError_eq_quadraticRemainder hp hp1 ψ z (-k) (neg_ne_zero.mpr hk)]
  change _ = -(b k*bn k)/(k : ℂ)^2+(b k*Qn k-bn k*Q k)/(k : ℂ)^3+
    (Q k*Qn k)/(k : ℂ)^4
  simp only [bn,Coeff.reflection_apply,Int.cast_neg]
  dsimp [b,sourceRootLinearFactorCoeff,Q,Qn,reflectedQuadraticRemainder]
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  field_simp
  ring


/-- One cutoff controls the actual-gap remainder uniformly near a source
and throughout a prescribed bounded spectral region. -/
theorem exists_uniform_sourceStandardRootQuadraticRemainder_tail_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (Rz : ℝ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ N : ℕ,
      ∀ ψ ∈ V, ∀ z : ℂ, ‖z‖ ≤ Rz → ∀ k : ℤ, N < k.natAbs →
        ‖sourceStandardRootQuadraticRemainder hp hp1 ψ z k‖ ≤
          (1/(2*Real.pi^2))*‖(canonicalPeriodicGap hp hp1
            (periodOnePotential ψ) (periodOnePotential_mem ψ) k)^2‖ := by
  obtain ⟨_,_,V,hVo,hφ,R,hR,hdata⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ
      (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N,hN⟩ := exists_nat_gt (2*(R+Rz)/Real.pi)
  refine ⟨V,hVo,hφ,N,?_⟩
  intro ψ hψ z hz k hk
  apply norm_sourceStandardRootQuadraticRemainder_tail_le hp hp1 ψ z k (by omega)
  have hmid := (hdata ψ hψ).1
  have hkr : (N : ℝ) < (k.natAbs : ℝ) := by exact_mod_cast hk
  have hlarge := (div_lt_iff₀ Real.pi_pos).mp (hN.trans hkr)
  have habs : |(k : ℝ)| = (k.natAbs : ℝ) := by simp
  rw [habs]
  linarith

/-- The source's final paired linear error is an actual lp coefficient divided by k. -/
theorem exists_sourceStandardRoot_paired_error_lp
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) :
    ∃ L : Coeff p, ∀ k : ℤ, k ≠ 0 →
      sourceStandardRootRelativeError hp hp1 ψ k z+
        sourceStandardRootRelativeError hp hp1 ψ (-k) z = L k/(k : ℂ) := by
  obtain ⟨L,R,h⟩ := exists_sourceStandardRoot_paired_error_coefficients hp hp1 ψ z
  have hhalf : p/2 ≤ p := by
    apply ENNReal.div_le_of_le_mul
    calc
      p = p*1 := by simp
      _ ≤ p*2 := by gcongr; norm_num
  have hRhalf := lp.memℓp R
  change Memℓp (fun k : ℤ => R k) (p/2) at hRhalf
  have hRp : Memℓp (fun k : ℤ => R k) p := hRhalf.of_exponent_ge hhalf
  have hR : Memℓp (fun k : ℤ => R k/(k : ℂ)) p := by
    apply hRp.norm.mono
    intro k
    by_cases hk : k = 0
    · simp [hk]
    · rw [norm_div,Complex.norm_intCast]
      apply div_le_self (norm_nonneg _)
      have hkabs : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
      exact_mod_cast hkabs
  let S : Coeff p := ⟨fun k => R k/(k : ℂ),hR⟩
  refine ⟨L+S,?_⟩
  intro k hk
  rw [h k hk]
  change L k/(k : ℂ)+R k/(k : ℂ)^2 = (L k+R k/(k : ℂ))/(k : ℂ)
  ring


/-- Pairing cancels the free spectral term and retains the literal midpoint difference. -/
theorem sourceStandardRootRelativeError_pair_eq_quadraticRemainder
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) (k : ℤ) (hk : k ≠ 0) :
    sourceStandardRootRelativeError hp hp1 ψ k z+
        sourceStandardRootRelativeError hp hp1 ψ (-k) z =
      (sourcePeriodicMidpointDisplacement hp hp1 ψ k-
        sourcePeriodicMidpointDisplacement hp hp1 ψ (-k))/((Real.pi : ℂ)*k)+
      (sourceStandardRootQuadraticRemainder hp hp1 ψ z k+
        sourceStandardRootQuadraticRemainder hp hp1 ψ z (-k))/(k : ℂ)^2 := by
  rw [sourceStandardRootRelativeError_eq_quadraticRemainder hp hp1 ψ z k hk,
    sourceStandardRootRelativeError_eq_quadraticRemainder hp hp1 ψ z (-k) (neg_ne_zero.mpr hk)]
  simp only [Int.cast_neg]
  ring

/-- Each factor error is bounded on every compact set avoiding its actual closed gap. -/
theorem exists_bound_sourceStandardRootRelativeError_on_compact
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (k : ℤ)
    (K : Set ℂ) (hK : IsCompact K) (hsub : K ⊆ (sourcePeriodicSegment hp hp1 ψ k)ᶜ) :
    ∃ C : ℝ, ∀ z ∈ K, ‖sourceStandardRootRelativeError hp hp1 ψ k z‖ ≤ C := by
  have hc : ContinuousOn (sourceStandardRootRelativeError hp hp1 ψ k) K :=
    (((sourceStandardRoot_analyticOnNhd hp hp1 ψ k).continuousOn.mono hsub).div_const
      ((Real.pi : ℂ)*k)).sub continuousOn_const
  obtain ⟨C,hC⟩ := (hK.image_of_continuousOn hc).isBounded.exists_norm_le
  exact ⟨C,fun z hz => hC _ (mem_image_of_mem _ hz)⟩


end NLS.ZakharovShabat
