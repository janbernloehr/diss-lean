import NLS.ZakharovShabat.SourcePeriodicGapSummability

/-!
# Locally uniform source squared-gap power tails

The squared-gap `p/2` power tail is exactly the `p` power of the ℓp
norm of the unsquared gap tail. Uniformly small endpoint tails therefore
give the locally uniform squared-gap asymptotic of Lemma 10.2(ii).
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Power tail of the canonical source squared-gap sequence beyond a
finite central block. -/
def sourcePeriodicSquaredGapPowerTail (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (M : ℕ) (n : ℤ) : ℝ :=
  if M < n.natAbs then
    ‖(canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2‖^
      (p.toReal/2)
  else 0

/-- The squared-gap power tail is summable, and its sum is exactly the
`p` power of the corresponding unsquared-gap ℓp tail norm. -/
theorem sourcePeriodicSquaredGapPowerTail_sum
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (M : ℕ) :
    Summable (sourcePeriodicSquaredGapPowerTail hp hp1 ψ M) ∧
      (∑' n : ℤ, sourcePeriodicSquaredGapPowerTail hp hp1 ψ M n) =
        ‖sourcePeriodicGapDisplacement hp hp1 ψ -
          Coeff.truncate (Finset.Icc (-(M : ℤ)) M)
            (sourcePeriodicGapDisplacement hp hp1 ψ)‖^p.toReal := by
  let g := sourcePeriodicGapDisplacement hp hp1 ψ
  let s := Finset.Icc (-(M : ℤ)) M
  have hpPos : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hmem (n : ℤ) : n ∈ s ↔ n.natAbs ≤ M := by
    simp only [s, Finset.mem_Icc]
    omega
  have hterm (n : ℤ) :
      sourcePeriodicSquaredGapPowerTail hp hp1 ψ M n =
        ‖(g-Coeff.truncate s g) n‖^p.toReal := by
    simp only [lp.coeFn_sub, Pi.sub_apply, Coeff.truncate_apply]
    by_cases hn : M < n.natAbs
    · have hs : n ∉ s := by simpa [hmem] using hn
      simp only [sourcePeriodicSquaredGapPowerTail, if_pos hn, if_neg hs, sub_zero]
      simpa only [g, sourcePeriodicGapDisplacement_apply] using
        (norm_sq_rpow_half (g n) p.toReal)
    · have hs : n ∈ s := (hmem n).mpr (by omega)
      simp only [sourcePeriodicSquaredGapPowerTail, if_neg hn, if_pos hs, sub_self,
        norm_zero, Real.zero_rpow hpPos.ne']
  have hsum : Summable (fun n : ℤ => ‖(g-Coeff.truncate s g) n‖^p.toReal) :=
    (lp.memℓp (g-Coeff.truncate s g)).summable hpPos
  constructor
  · exact hsum.congr (fun n => (hterm n).symm)
  · calc
      (∑' n : ℤ, sourcePeriodicSquaredGapPowerTail hp hp1 ψ M n) =
          ∑' n : ℤ, ‖(g-Coeff.truncate s g) n‖^p.toReal := tsum_congr hterm
      _ = ‖g-Coeff.truncate s g‖^p.toReal := (lp.norm_rpow_eq_tsum hpPos _).symm

/-- Around every source potential, the actual gap sequence has a common
ℓp norm bound and uniformly small ℓp tails. -/
theorem exists_uniform_small_sourcePeriodicGapDisplacement
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ ψ ∈ V,
        ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ ≤ R ∧
        ∀ M : ℕ, N ≤ M →
          ‖sourcePeriodicGapDisplacement hp hp1 ψ -
            Coeff.truncate (Finset.Icc (-(M : ℤ)) M)
              (sourcePeriodicGapDisplacement hp hp1 ψ)‖ ≤ ε := by
  obtain ⟨N, hN, U, hUopen, _, hφU, _, R, hR, hdata⟩ :=
    exists_uniform_small_canonicalPeriodicDisplacements hp hp1
      (periodOnePotential φ) (half_pos hε)
  let V : Set (CoeffPair p) := periodOnePotential ⁻¹' U
  refine ⟨N, hN, V, hUopen.preimage (periodOnePotential (p := p)).continuous,
    hφU, 2*R, by positivity, ?_⟩
  intro ψ hψ
  let a := canonicalPeriodicLeftDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let b := canonicalPeriodicRightDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  obtain ⟨ha, hb, htail⟩ := hdata (periodOnePotential ψ) hψ (periodOnePotential_mem ψ)
  have hbound : ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ ≤ 2*R := by
    change ‖b-a‖ ≤ 2*R
    nlinarith [norm_sub_le b a]
  refine ⟨hbound, ?_⟩
  intro M hM
  let s := Finset.Icc (-(M : ℤ)) M
  have heq : sourcePeriodicGapDisplacement hp hp1 ψ -
      Coeff.truncate s (sourcePeriodicGapDisplacement hp hp1 ψ) =
        (b-Coeff.truncate s b)-(a-Coeff.truncate s a) := by
    ext n
    by_cases hn : n ∈ s
    · simp only [lp.coeFn_sub, Pi.sub_apply, Coeff.truncate_apply,
        if_pos hn, sub_self]
    · simp only [lp.coeFn_sub, Pi.sub_apply, Coeff.truncate_apply,
        if_neg hn, sub_zero]
      rfl
  rw [heq]
  obtain ⟨hta, htb⟩ := htail M hM
  have hsub := norm_sub_le (b-Coeff.truncate s b) (a-Coeff.truncate s a)
  dsimp only [a, b, s] at hta htb ⊢
  linarith

/-- The canonical squared-gap `p/2` power tails are uniformly small on
one source neighborhood around any parameter. -/
theorem exists_uniform_small_sourcePeriodicSquaredGapPowerTail
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ M : ℕ, N ≤ M →
        Summable (sourcePeriodicSquaredGapPowerTail hp hp1 ψ M) ∧
        (∑' n : ℤ, sourcePeriodicSquaredGapPowerTail hp hp1 ψ M n) ≤ ε^p.toReal := by
  obtain ⟨N, hN, V, hVopen, hφV, R, hR, hdata⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ hε
  refine ⟨N, hN, V, hVopen, hφV, ?_⟩
  intro ψ hψ M hM
  have h := sourcePeriodicSquaredGapPowerTail_sum hp hp1 ψ M
  refine ⟨h.1, ?_⟩
  rw [h.2]
  have htail := (hdata ψ hψ).2 M hM
  exact Real.rpow_le_rpow (norm_nonneg _) htail ENNReal.toReal_nonneg

end NLS.ZakharovShabat
