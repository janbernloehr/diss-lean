import NLS.ZakharovShabat.SourcePsiRefinedQuotientTail
import NLS.ZakharovShabat.SourcePsiMidpointFilledFactorMajorant

/-! # Refined chi tail estimates for the actual normalized roots

The quotient error retains its chosen exponent. The denominator adds
only a translated reciprocal lattice, whose norm is independent of the
deleted index. The source domain and tail cutoff precede the exponent.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A quotient majorant at any exponent above one gives a chi majorant
at that same exponent; it need not equal the source exponent. -/
theorem exists_sourcePsiMidpointFilledRegularFactor_refinedTailMajorant_of_quotient
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr1 : 1 < r) (B : Coeff r) (D : ℝ) (hD : 0 ≤ D) (K : ℕ)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi : ℂ)*n‖ ≤ D)
    (hsep : ∀ m : ℤ, K ≤ m.natAbs → m ≠ n →
      ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
        (Real.pi/2)*|((n-m : ℤ) : ℝ)| ≤ ‖sourceStandardRootMidpoint hp hp1 ψ n-z‖)
    (hquot : ∀ m : ℤ, K ≤ m.natAbs → m ≠ n →
      ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
        ‖sourceSingleRootQuotientJointProduct hp hp1 m
          (z,(sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n),ψ))-1‖ ≤ ‖B m‖) :
    ∃ E : Coeff r,
      ‖E‖ ≤ 2*‖B‖+(2/Real.pi)*(D+Real.pi/8)*‖Coeff.puncturedLattice r hr1‖ ∧
      ∀ m : ℤ, K ≤ m.natAbs → m ≠ n →
        ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
          ‖sourcePsiMidpointFilledRegularFactor hp hp1 n m a ψ z-I‖ ≤ ‖E m‖ := by
  let L := Coeff.shift n (Coeff.puncturedLattice r hr1)
  let c : ℝ := (2/Real.pi)*(D+Real.pi/8)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let E : Coeff r := (2 : ℂ) • Coeff.magnitude B+(c : ℂ) • Coeff.magnitude L
  have hEpoint m : ‖E m‖ = 2*‖B m‖+c*‖L m‖ := by
    simp only [E,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,
      Coeff.magnitude_apply,smul_eq_mul]
    change ‖((2 : ℝ) : ℂ)*(‖B m‖ : ℂ)+(c : ℂ)*(‖L m‖ : ℂ)‖ = _
    rw [← Complex.ofReal_mul,← Complex.ofReal_mul,← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  refine ⟨E,?_,?_⟩
  · calc
      ‖E‖ ≤ ‖(2 : ℂ) • Coeff.magnitude B‖+‖(c : ℂ) • Coeff.magnitude L‖ := norm_add_le _ _
      _ = 2*‖B‖+c*‖Coeff.puncturedLattice r hr1‖ := by
        simp only [norm_smul,Coeff.norm_magnitude,Complex.norm_ofNat,
          Complex.norm_real,Real.norm_of_nonneg hc,L,Coeff.norm_shift]
      _ = _ := rfl
  · intro m hm hmn z hz
    have hL : ‖L m‖ = |((n-m : ℤ) : ℝ)|⁻¹ := by
      simp only [L,Coeff.shift_apply,Coeff.puncturedLattice_apply,if_neg (sub_ne_zero.mpr hmn),
        norm_inv,Complex.norm_intCast]
      simp only [Int.cast_sub,abs_sub_comm]
    rw [hEpoint,hL]
    have hB : ‖sourceSingleRootQuotientJointProduct hp hp1 m
        (z,(sourcePsiFillDeletedRoot n a (sourceStandardRootMidpoint hp hp1 ψ n),ψ))-1‖ ≤
          ‖(lp.single p m (B m) : Coeff p) m‖ := by
      simpa only [lp.single_apply,Pi.single_eq_same] using hquot m hm hmn z hz
    simpa only [c,div_eq_mul_inv,lp.single_apply,Pi.single_eq_same] using
      norm_sourcePsiMidpointFilledRegularFactor_sub_I_le hp hp1 n m hmn a ψ (lp.single p m (B m))
        D (Real.pi/8) hD (by positivity) hmid z hz (hsep m hm hmn z hz) hB

/-- The actual chi error has a locally uniform tail majorant for every
finite exponent above one and at least p/2, uniformly in the deleted index. -/
theorem SourcePsiSquaredGapComplexExtension.exists_local_refined_chi_tail_majorants
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ V) :
    ∃ T : Set (CoeffPair p), IsOpen T ∧ φ.val ∈ T ∧ T ⊆ V ∧ ∃ K : ℕ,
      ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ∀ n : ℤ, ∃ B : Coeff r, ‖B‖ ≤ M ∧
          ∀ k : ℤ, K ≤ k.natAbs → k ≠ n → ∀ z ∈ closedBall ((Real.pi:ℂ)*k) (Real.pi/8),
            ‖sourcePsiMidpointFilledRegularFactor hp hp1 n k (s n ψ) ψ z-Complex.I‖ ≤ ‖B k‖ := by
  obtain ⟨N,ε,_,T,hT,hφT,hTV,Kq,hNKq,hquot⟩ := hs.exists_local_refined_quotient_tail_majorants φ hφ
  obtain ⟨G,hG,hφG,D,hD,Km,hmiddata⟩ := exists_local_sourcePeriodicMidpoint_tail_lattice_separation hp hp1 φ.val
  let K := max Km Kq
  refine ⟨T ∩ G,hT.inter hG,⟨hφT,hφG⟩,fun _ h => hTV h.1,K,?_⟩
  intro r hr hr1 hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  obtain ⟨M,hM,hbound⟩ := hquot r hr hr1 hpr
  let C := 2*M+(2/Real.pi)*(D+Real.pi/8)*‖Coeff.puncturedLattice r hr1‖
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro ψ hψ n
  obtain ⟨B,hB,hBpoint⟩ := hbound ψ hψ.1 n
  obtain ⟨hmidnorm,hsep⟩ := hmiddata ψ hψ.2
  have hmid : ‖sourceStandardRootMidpoint hp hp1 ψ n-(Real.pi:ℂ)*n‖ ≤ D := by
    have h := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      (sourcePeriodicMidpointDisplacement hp hp1 ψ) n).trans hmidnorm
    simpa only [sourcePeriodicMidpointDisplacement_apply,sourceStandardRootMidpoint] using h
  obtain ⟨E,hE,hEpoint⟩ := exists_sourcePsiMidpointFilledRegularFactor_refinedTailMajorant_of_quotient
    hp hp1 n (s n ψ) ψ hr1 B D hD K hmid
    (fun k hk hkn z hz => hsep k ((le_max_left Km Kq).trans hk) n hkn.symm z hz) (by
      intro k hk _ z hz
      have hkq : Kq ≤ k.natAbs := (le_max_right Km Kq).trans hk
      have hkn : ¬k.natAbs ≤ N := by omega
      apply hBpoint k hkq z
      simp only [sourceIsolatingDisc,if_neg hkn]
      exact (mem_closedBall.mp hz).trans_lt (by linarith [Real.pi_pos]))
  refine ⟨E,hE.trans ?_,hEpoint⟩
  dsimp only [C]
  linarith

end NLS.ZakharovShabat
