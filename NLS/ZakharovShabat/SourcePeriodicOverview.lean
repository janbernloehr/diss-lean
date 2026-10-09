import NLS.ZakharovShabat.SourcePeriodicGapTails

/-! # Theorem 1.2 and Corollary 1.3 in the original source space

The endpoints below are the canonical lexicographically ordered eigenvalues,
including their original algebraic multiplicities. The literal sum in
Theorem 1.2 is bounded on one neighborhood in the source coefficient norm.
Corollary 1.3 uses the same endpoints and supplies a common neighborhood for
the midpoint and gap estimates. All finite exponents greater than one are
covered; these results do not require the unresolved printed-height bound.
-/
noncomputable section
open Set
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The summand in the printed Theorem 1.2, with the actual ordered endpoints. -/
def sourcePeriodicEndpointEnergy (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) : ℝ :=
  ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n -
    (Real.pi : ℂ)*n‖^p.toReal +
  ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n -
    (Real.pi : ℂ)*n‖^p.toReal

/-- The printed series is summable, and equals the two full displacement energies. -/
theorem sourcePeriodicEndpointEnergy_sum (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    Summable (sourcePeriodicEndpointEnergy hp hp1 ψ) ∧
      (∑' n : ℤ, sourcePeriodicEndpointEnergy hp hp1 ψ n) =
        ‖canonicalPeriodicLeftDisplacement hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ)‖^p.toReal +
        ‖canonicalPeriodicRightDisplacement hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ)‖^p.toReal := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  let a := canonicalPeriodicLeftDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let b := canonicalPeriodicRightDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
  have ha := (lp.memℓp a).summable hp0
  have hb := (lp.memℓp b).summable hp0
  exact ⟨ha.add hb, (ha.tsum_add hb).trans (by
    rw [← lp.norm_rpow_eq_tsum hp0 a, ← lp.norm_rpow_eq_tsum hp0 b])⟩

/-- Theorem 1.2: one positive bound for the full printed sum on a source neighborhood. -/
theorem sourceTheorem1_2 (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ C : ℝ, 0 < C ∧ ∀ ψ ∈ U,
        Summable (sourcePeriodicEndpointEnergy hp hp1 ψ) ∧
        (∑' n : ℤ, sourcePeriodicEndpointEnergy hp hp1 ψ n) ≤ C := by
  obtain ⟨V,ho,hconv,hφ,h0,R,hR,hbound⟩ :=
    exists_uniform_bounded_canonicalPeriodicDisplacements hp hp1 (periodOnePotential φ)
  refine ⟨periodOnePotential ⁻¹' V,ho.preimage (periodOnePotential (p := p)).continuous,
    hconv.linear_preimage ((periodOnePotential (p := p)).restrictScalars ℝ).toLinearMap,
    hφ,by simpa only [mem_preimage,map_zero] using h0,2*R^p.toReal+1,by positivity,?_⟩
  intro ψ hψ
  obtain ⟨ha,hb⟩ := hbound (periodOnePotential ψ) hψ (periodOnePotential_mem ψ)
  obtain ⟨hsum,he⟩ := sourcePeriodicEndpointEnergy_sum hp hp1 ψ
  refine ⟨hsum,?_⟩
  rw [he]
  have hla := Real.rpow_le_rpow (norm_nonneg _) ha (show 0 ≤ p.toReal from ENNReal.toReal_nonneg)
  have hlb := Real.rpow_le_rpow (norm_nonneg _) hb (show 0 ≤ p.toReal from ENNReal.toReal_nonneg)
  linarith

/-- The labels used by Theorem 1.2 are globally ordered and preserve every
central and distant algebraic multiplicity in the original periodic spectrum. -/
theorem sourceTheorem1_2_ordered_labels (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    ∃ N : ℕ,
      PeriodicEndpointLabeling hp (periodOnePotential ψ) N
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ))
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) ∧
      (∀ n : ℤ, complexLexLE
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)) ∧
      ∀ i j : ℤ, i < j → complexLexLE
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) i)
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j) :=
  ⟨_,canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)⟩

/-- Corollary 1.3: the actual midpoint displacement and gap belong to ℓp. -/
theorem sourceCorollary1_3_mem (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    Memℓp (fun n : ℤ => canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n - (Real.pi : ℂ)*n) p ∧
    Memℓp (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) p := by
  constructor
  · convert lp.memℓp (sourcePeriodicMidpointDisplacement hp hp1 ψ) using 1
    exact (funext (sourcePeriodicMidpointDisplacement_apply hp hp1 ψ)).symm
  · convert lp.memℓp (sourcePeriodicGapDisplacement hp hp1 ψ) using 1
    exact (funext (sourcePeriodicGapDisplacement_apply hp hp1 ψ)).symm

/-- Corollary 1.3 locally uniformly: one neighborhood, norm bound, and cutoff
work for both sequences, with arbitrarily small tails and every larger cutoff. -/
theorem sourceCorollary1_3 (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      ∃ R : ℝ, 0 < R ∧ ∀ ψ ∈ U,
        ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ R ∧
        ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ ≤ R ∧
        ∀ M : ℕ, N ≤ M →
          ‖sourcePeriodicMidpointDisplacement hp hp1 ψ -
            Coeff.truncate (Finset.Icc (-(M : ℤ)) M)
              (sourcePeriodicMidpointDisplacement hp hp1 ψ)‖ ≤ ε ∧
          ‖sourcePeriodicGapDisplacement hp hp1 ψ -
            Coeff.truncate (Finset.Icc (-(M : ℤ)) M)
              (sourcePeriodicGapDisplacement hp hp1 ψ)‖ ≤ ε := by
  obtain ⟨Nm,hNm,Um,hUm,hφm,Rm,hRm,hm⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ hε
  obtain ⟨Ng,hNg,Ug,hUg,hφg,Rg,hRg,hg⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ hε
  refine ⟨max Nm Ng,hNm.trans (le_max_left _ _),Um ∩ Ug,hUm.inter hUg,⟨hφm,hφg⟩,
    Rm+Rg+1,by positivity,?_⟩
  intro ψ hψ
  obtain ⟨hmb,hmt⟩ := hm ψ hψ.1
  obtain ⟨hgb,hgt⟩ := hg ψ hψ.2
  refine ⟨hmb.trans (by linarith),hgb.trans (by linarith),fun M hM => ?_⟩
  exact ⟨hmt M ((le_max_left _ _).trans hM),hgt M ((le_max_right _ _).trans hM)⟩

end NLS.ZakharovShabat
