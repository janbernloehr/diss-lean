import NLS.ZakharovShabat.SourcePsiMidpointDenominator
import NLS.ZakharovShabat.SourcePsiQuadraticRootOffset
import NLS.ZakharovShabat.SourcePsiQuotientQuantitativeDisc
import NLS.SequenceSpaces.PuncturedLattice

/-!
# Uniform lp error majorants for the actual midpoint-filled chi

Equation (2.32) follows from the existing quotient error majorants
and the omitted-midpoint denominator estimate. The additional error
is a translated reciprocal lattice, whose lp norm is independent of
the deleted index. The quotient is evaluated at the actual filled
root sequence, with its norm controlled uniformly by the original
deleted root input and the source midpoint displacement.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Quotient error and omitted-midpoint separation control chi's
error from i on a selected free-centered disc. -/
theorem norm_sourcePsiMidpointFilledRegularFactor_sub_I_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (hmn : m ≠ n)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (B : Coeff p)
    (D R : ℝ) (hD : 0 ≤ D) (hR : 0 ≤ R)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi : ℂ)*n‖ ≤ D)
    (z : ℂ) (hz : z ∈ closedBall ((Real.pi : ℂ)*m) R)
    (hsep : (Real.pi/2)*|((n-m : ℤ) : ℝ)| ≤
      ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖)
    (hquot : ‖sourceSingleRootQuotientJointProduct hp hp1 m
      (z,(sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n),ψ))-1‖ ≤ ‖B m‖) :
    ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ z-I‖ ≤
      2*‖B m‖+(2/Real.pi)*(D+R)/|((n-m : ℤ) : ℝ)| := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let d := τ-z
  let k : ℂ := (Real.pi : ℂ)*((n-m : ℤ) : ℂ)
  let r := k/d
  let Q := sourceSingleRootQuotientJointProduct hp hp1 m
    (z,(sourcePsiFillDeletedRoot n a τ,ψ))
  have habs : 0 < |((n-m : ℤ) : ℝ)| := by
    exact_mod_cast abs_pos.mpr (sub_ne_zero.mpr hmn.symm)
  have hlow : 0 < (Real.pi/2)*|((n-m : ℤ) : ℝ)| := by positivity
  have hd : 0 < ‖d‖ := hlow.trans_le hsep
  have hdne : d ≠ 0 := norm_pos_iff.mp hd
  have hk : ‖k‖ = Real.pi*|((n-m : ℤ) : ℝ)| := by
    simp only [k,norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_intCast]
  have hr : ‖r‖ ≤ 2 := by
    rw [show ‖r‖ = ‖k‖/‖d‖ from norm_div _ _,hk]
    have h := div_le_div₀ (by positivity : 0 ≤ Real.pi*|((n-m : ℤ) : ℝ)|) le_rfl hlow hsep
    convert h using 1 <;> (first | rfl | field_simp)
  have hzR : ‖z-(Real.pi : ℂ)*m‖ ≤ R := by
    simpa only [mem_closedBall,dist_eq_norm] using hz
  have hkd : ‖k-d‖ ≤ D+R := by
    have heq : k-d = ((Real.pi : ℂ)*n-τ)+(z-(Real.pi : ℂ)*m) := by
      simp only [k,d,Int.cast_sub]
      ring
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add (by simpa only [norm_sub_rev] using hmid) hzR)
  have hrerror : ‖r-1‖ ≤ (2/Real.pi)*(D+R)/|((n-m : ℤ) : ℝ)| := by
    have heq : r-1 = (k-d)/d := by dsimp only [r]; field_simp [hdne]
    rw [heq,norm_div]
    have h := div_le_div₀ (add_nonneg hD hR) hkd hlow hsep
    convert h using 1 <;> (first | rfl | ring)
  have hchi : sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ z-I =
      I*(r*(Q-1)+(r-1)) := by
    simp only [sourcePsiMidpointFilledRegularFactor,sourcePsiGapRegularFactor,
      displacedRoots_sourcePsiFillDeletedRoot_same]
    dsimp only [r,k,d,Q,τ]
    ring
  rw [hchi,norm_mul,norm_I,one_mul]
  calc
    ‖r*(Q-1)+(r-1)‖ ≤ ‖r‖*‖Q-1‖+‖r-1‖ := by
      simpa only [norm_mul] using norm_add_le (r*(Q-1)) (r-1)
    _ ≤ 2*‖B m‖+(2/Real.pi)*(D+R)/|((n-m : ℤ) : ℝ)| :=
      add_le_add (mul_le_mul hr hquot (norm_nonneg _) (by norm_num)) hrerror

/-- A quotient lp majorant yields an actual chi-error majorant.
The extra reciprocal-lattice norm is independent of the deleted index. -/
theorem exists_sourcePsiMidpointFilledRegularFactor_tailMajorant_of_quotient
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (B : Coeff p) (D : ℝ) (hD : 0 ≤ D) (K : ℕ)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi : ℂ)*n‖ ≤ D)
    (hsep : ∀ m : ℤ, K ≤ m.natAbs → m ≠ n →
      ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
        (Real.pi/2)*|((n-m : ℤ) : ℝ)| ≤ ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖)
    (hquot : ∀ m : ℤ, K ≤ m.natAbs → m ≠ n →
      ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
        ‖sourceSingleRootQuotientJointProduct hp hp1 m
          (z,(sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n),ψ))-1‖ ≤ ‖B m‖) :
    ∃ E : Coeff p,
      ‖E‖ ≤ 2*‖B‖+(2/Real.pi)*(D+Real.pi/8)*‖Coeff.puncturedLattice p hp1‖ ∧
      ∀ m : ℤ, K ≤ m.natAbs → m ≠ n →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
          ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ z-I‖ ≤ ‖E m‖ := by
  let L := Coeff.shift n (Coeff.puncturedLattice p hp1)
  let c : ℝ := (2/Real.pi)*(D+Real.pi/8)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let E : Coeff p := (2 : ℂ) • Coeff.magnitude B+(c : ℂ) • Coeff.magnitude L
  have hEpoint m : ‖E m‖ = 2*‖B m‖+c*‖L m‖ := by
    simp only [E,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,
      Coeff.magnitude_apply,smul_eq_mul]
    change ‖((2 : ℝ) : ℂ)*(‖B m‖ : ℂ)+(c : ℂ)*(‖L m‖ : ℂ)‖ = _
    rw [← Complex.ofReal_mul,← Complex.ofReal_mul,← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  refine ⟨E,?_,?_⟩
  · calc
      ‖E‖ ≤ ‖(2 : ℂ) • Coeff.magnitude B‖+‖(c : ℂ) • Coeff.magnitude L‖ := norm_add_le _ _
      _ = 2*‖B‖+c*‖Coeff.puncturedLattice p hp1‖ := by
        simp only [norm_smul,Coeff.norm_magnitude,Complex.norm_ofNat,
          Complex.norm_real,Real.norm_of_nonneg hc,L,Coeff.norm_shift]
      _ = _ := rfl
  · intro m hm hmn z hz
    have hL : ‖L m‖ = |((n-m : ℤ) : ℝ)|⁻¹ := by
      simp only [L,Coeff.shift_apply,Coeff.puncturedLattice_apply,if_neg (sub_ne_zero.mpr hmn),
        norm_inv,Complex.norm_intCast]
      simp only [Int.cast_sub,abs_sub_comm]
    rw [hEpoint,hL]
    simpa only [c,div_eq_mul_inv] using
      norm_sourcePsiMidpointFilledRegularFactor_sub_I_le hp hp1 n m hmn a ψ B
        D (Real.pi/8) hD (by positivity) hmid z hz (hsep m hm hmn z hz) (hquot m hm hmn z hz)

/-- Equation (2.32) on free-centered tail discs, with a norm bound
uniform in the deleted index, source, and every bounded root input.
Both quotient and denominator estimates are instantiated by the actual
source data; no chi bound or root asymptotic is assumed. -/
theorem exists_local_sourcePsiMidpointFilledRegularFactor_uniformBoundedBallTailMajorant
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (T : ℝ) (hT : 0 ≤ T) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ ψ ∈ V, ∀ n : ℤ, ∀ a : DeletedCoeff p n, ‖a‖ ≤ T →
          ∃ E : Coeff p, ‖E‖ ≤ C ∧
            ∀ m : ℤ, K ≤ m.natAbs → m ≠ n →
              ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
                ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ z-I‖ ≤ ‖E m‖ := by
  obtain ⟨Vm,hVm,hφm,D,hD,Km,hmiddata⟩ :=
    exists_local_sourcePeriodicMidpoint_tail_lattice_separation hp hp1 φ
  obtain ⟨N,ε,hε,Vq,hVq,hφq,Kq,hNKq,M,hM,hquotdata⟩ :=
    exists_local_sourcePsiQuotient_uniformBoundedBallTailMajorant hp hp1 φ hφ
      (T+D) (add_nonneg hT hD)
  let V := Vm ∩ Vq
  let K := max Km Kq
  let C := 2*M+(2/Real.pi)*(D+Real.pi/8)*‖Coeff.puncturedLattice p hp1‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨V,hVm.inter hVq,⟨hφm,hφq⟩,K,C,hC,?_⟩
  intro ψ hψ n a ha
  obtain ⟨hmidnorm,hsep⟩ := hmiddata ψ hψ.1
  have hmid : ‖sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi : ℂ)*n‖ ≤ D := by
    have h := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      (sourcePeriodicMidpointDisplacement hp hp1 ψ) n).trans hmidnorm
    simpa only [sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] using h
  let b := sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n)
  have hb : ‖b‖ ≤ T+D := by
    let v : Coeff p := lp.single p n
      (sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi : ℂ)*n)
    have hv : ‖v‖ ≤ D := by
      rw [show ‖v‖ = ‖sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi : ℂ)*n‖ from
        lp.norm_single (zero_lt_one.trans_le (Fact.out : 1 ≤ p)) n _]
      exact hmid
    exact (norm_add_le (a : Coeff p) v).trans (add_le_add ha hv)
  obtain ⟨B,hB,hBpoint⟩ := hquotdata ψ hψ.2 b hb
  have hsepK m (hm : K ≤ m.natAbs) (hmn : m ≠ n) z hz :=
    hsep m ((le_max_left Km Kq).trans hm) n hmn.symm z hz
  have hquotK m (hm : K ≤ m.natAbs) (_hmn : m ≠ n) z
      (hz : z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8)) :
      ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,(b,ψ))-1‖ ≤ ‖B m‖ := by
    have hmKq : Kq ≤ m.natAbs := (le_max_right Km Kq).trans hm
    have hmN : ¬m.natAbs ≤ N := by omega
    have hzdisc : z ∈ sourceIsolatingDisc hp hp1 φ N ε m := by
      simp only [sourceIsolatingDisc,if_neg hmN]
      exact (mem_closedBall.mp hz).trans_lt (by linarith [Real.pi_pos])
    exact hBpoint m hmKq z hzdisc
  obtain ⟨E,hE,hEpoint⟩ := exists_sourcePsiMidpointFilledRegularFactor_tailMajorant_of_quotient
    hp hp1 n a ψ B D hD K hmid hsepK hquotK
  refine ⟨E,hE.trans ?_,hEpoint⟩
  dsimp only [C]
  linarith

end NLS.ZakharovShabat
