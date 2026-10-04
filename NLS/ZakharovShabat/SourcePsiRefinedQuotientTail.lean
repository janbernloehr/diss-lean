import NLS.ZakharovShabat.SourcePsiRefinedOffsetExponent
import NLS.ZakharovShabat.SourceSingleRootQuotientAsymptoticDiscSup

/-! # Refined tail bounds for the actual normalized psi quotient

The midpoint-filled actual root sequence has the refined displacement
exponents. Lemma 10.8 then gives quotient error majorants uniformly in
the deleted index. The neighborhood and tail threshold precede the
auxiliary exponent; only the norm bound depends on that exponent.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Actual quotient tail errors have every finite exponent above one
and at least p/2. A single source neighborhood and cutoff work for all
exponents and all deleted indices. -/
theorem SourcePsiSquaredGapComplexExtension.exists_local_refined_quotient_tail_majorants
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 V s)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ V) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∃ T : Set (CoeffPair p),
      IsOpen T ∧ φ.val ∈ T ∧ T ⊆ V ∧ ∃ K : ℕ, N < K ∧
        ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
          ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ T, ∀ n : ℤ, ∃ B : Coeff r, ‖B‖ ≤ M ∧
            ∀ k : ℤ, K ≤ k.natAbs → ∀ z ∈ sourceIsolatingDisc hp hp1 φ.val N ε k,
              ‖sourceSingleRootQuotientJointProduct hp hp1 k
                (z,(sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n),ψ))-1‖ ≤ ‖B k‖ := by
  obtain ⟨T,hT,hφT,hTV,L,hL,hoff⟩ := hs.locally_uniform_refined_filled_offsets φ.val hφ
  obtain ⟨N,ε,hε,_,G,hG,_,hφG,C,R,H,hC,hR,_,K,hNK,hdata⟩ :=
    exists_local_sourceSingleRootQuotientAsymptotic_data hp hp1 φ.val φ.property
  refine ⟨N,ε,hε,T ∩ G,hT.inter hG,⟨hφT,hφG⟩,fun _ h => hTV h.1,K,hNK,?_⟩
  intro r hr hr1 hpr
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  have hhalf : 0 < ENNReal.ofReal (p.toReal/2) :=
    ENNReal.ofReal_pos.mpr (div_pos (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp) (by norm_num))
  let f : ℝ × ℝ → ℝ := fun t =>
    (Real.pi⁻¹*(Fourier.hilbertTransformBound hr1 hr+‖Fourier.hilbertSquareCoeffs‖)+
      C*R*‖Fourier.hilbertSquareCoeffs‖)*t.1 +
    Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hr*t.1)*
      ((C/2)*Fourier.absoluteSampledRowConstant hr*t.1)^2 +
    (Real.exp (C*t.1*‖Coeff.puncturedLattice r.conjExponent
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt r r.conjExponent).mp hr.lt_top)‖)*C^2) *
      (t.2*‖squaredReciprocalKernel (min 1 (p.toReal/2))
        (lt_min (by norm_num : (1/2:ℝ)<1) (by
          have hpt : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
          linarith))‖)
  have hf : Continuous f := by dsimp only [f]; fun_prop
  obtain ⟨M,hM⟩ := ((show IsCompact (Icc (0:ℝ) L ×ˢ Icc (0:ℝ) (H^2)) from
    isCompact_Icc.prod isCompact_Icc).image hf).bddAbove
  refine ⟨max 0 M,le_max_left _ _,?_⟩
  intro ψ hψ n
  obtain ⟨β,hβ,hβnorm⟩ := hoff ψ hψ.1 n r hr hr1 hpr
  let a := sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n)
  obtain ⟨hdisp,hgap,hsep,hsmall,hdom⟩ := hdata ψ hψ.2
  obtain ⟨Br,Bg,hpoint,hBr,hBg⟩ := exists_sourceSingleRootQuotientDiscMajorants hp hp1 hr1 hr
    φ.val ψ a β hβ N K ε C R hC hR hdisp hsep (hdom a) hsmall
  let BgR : Coeff r := ⟨fun k => Bg k,(lp.memℓp Bg).of_exponent_ge hpr⟩
  let B := Coeff.magnitude Br+Coeff.magnitude BgR
  have hBpoint (k : ℤ) : ‖B k‖ = ‖Br k‖+‖Bg k‖ := by
    simp only [B,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply,BgR]
    rw [← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have hBnorm : ‖B‖ ≤ ‖Br‖+‖Bg‖ := by
    calc
      ‖B‖ ≤ ‖Coeff.magnitude Br‖+‖Coeff.magnitude BgR‖ := norm_add_le _ _
      _ = ‖Br‖+‖BgR‖ := by simp
      _ ≤ ‖Br‖+‖Bg‖ := add_le_add le_rfl
        (Coeff.norm_quasiExponentInclusion_le hhalf (zero_lt_one.trans hr1) hr hpr Bg)
  refine ⟨B,?_,?_⟩
  · calc
      ‖B‖ ≤ ‖Br‖+‖Bg‖ := hBnorm
      _ ≤ f (‖β‖,‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖) := add_le_add hBr hBg
      _ ≤ M := hM ⟨(‖β‖,‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖),
        ⟨⟨lp.norm_nonneg' _,hβnorm⟩,⟨lp.norm_nonneg' _,hgap⟩⟩,rfl⟩
      _ ≤ max 0 M := le_max_right _ _
  · intro k hk z hz
    rw [hBpoint]
    exact hpoint k (by omega) z hz

end NLS.ZakharovShabat
