import NLS.ZakharovShabat.SourcePsiShiftedDiscLatticeBound

/-!
# Uniform regular-factor majorants for distant deleted indices

For a fixed real-type source, finitely many shifted head circles have
one lattice-distance cutoff. Beyond that deleted index, the same
`ℓᵖ` quotient majorant controls the weighted regular factor on every
selected circle, including all free-centered tail circles.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A common parameter neighborhood and majorant norm control all
weighted psi regular factors when the deleted index is sufficiently
distant. The selected contour family is independent of that index. -/
theorem exists_local_sourcePsi_distantDeleted_uniformRegularFactorMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ N K : ℕ, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        (∀ m : ℤ, (c m).im = 0) ∧
        (∀ m : ℤ, K < m.natAbs →
          c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
        (∀ t ∈ U, ∀ m : ℤ,
          0 < R m ∧
          sourcePeriodicSegment hp hp1 t.2 m ⊆ ball (c m) (R m) ∧
          closedBall (c m) (R m) ⊆
            sourceStandardRootOmittedDomain hp hp1 t.2 m ∧
          sphere (c m) (R m) ⊆
            sourceCanonicalRootDomain hp hp1 t.2) ∧
        (∃ Niso : ℕ, ∃ εiso : ℝ,
          (∀ t ∈ U, ∀ m : ℤ,
            sourceSpectralCluster hp hp1 t.2 m ⊆
              sourceIsolatingDisc hp hp1 φ Niso εiso m) ∧
          (∀ i j : ℤ, i ≠ j →
            Disjoint (sourceIsolatingDisc hp hp1 φ Niso εiso i)
              (sourceIsolatingDisc hp hp1 φ Niso εiso j)) ∧
          ∀ m : ℤ, closedBall (c m) (R m) ⊆
            sourceIsolatingDisc hp hp1 φ Niso εiso m) ∧
        ∃ M : ℝ, 0 ≤ M ∧
          ∀ n : ℤ, N ≤ n.natAbs →
            ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
              ((a : Coeff p),ψ) ∈ U →
                ∃ B : Coeff p, ‖B‖ ≤ M ∧
                  ∀ m : ℤ, m ≠ n →
                    ∀ z ∈ closedBall (c m) (R m),
                      ‖(((n-m : ℤ) : ℂ) *
                        sourcePsiGapRegularFactor hp hp1 n m
                          (a : Coeff p) ψ z)‖ ≤
                        (2/Real.pi)*(1+‖B m‖) := by
  obtain ⟨U,hUopen,hbase,K,c,R,hcReal,hchoice,hgeom,hiso,M,hM,hmajor⟩ :=
    exists_local_sourcePsiQuotient_uniformAllSelectedDiscMajorant
      hp hp1 φ hφ a₀
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  have hRhead (m : ℤ) (hm : m ∈ s) : 0 ≤ R m :=
    (hgeom (a₀,φ) hbase m).1.le
  obtain ⟨L,hL⟩ := exists_uniform_shifted_disc_lattice_cutoff
    s c R hRhead
  let N : ℕ := K+L+1
  refine ⟨U,hUopen,hbase,N,K,c,R,hcReal,hchoice,hgeom,hiso,M,hM,?_⟩
  intro n hn a ψ hpair
  obtain ⟨B,hBnorm,hB⟩ := hmajor ((a : Coeff p),ψ) hpair
  refine ⟨B,hBnorm,?_⟩
  intro m hmn z hz
  by_cases hm : m ∈ s
  · have hmK : m.natAbs ≤ K := by
      simp only [s,Finset.mem_Icc] at hm
      omega
    have htri : n.natAbs ≤ (n-m).natAbs + m.natAbs := by
      have h := Int.natAbs_add_le (n-m) m
      simpa only [sub_add_cancel] using h
    have hdist : L ≤ (n-m).natAbs := by
      dsimp [N] at hn
      omega
    exact norm_deletedPsi_gapRegularFactor_weighted_le_on_shifted_disc
      hp hp1 n m (Ne.symm hmn) a ψ B (c m) (R m)
        (hL m hm n hdist) z hz (hB m z hz)
  · have hmK : K < m.natAbs := by
      simp only [s,Finset.mem_Icc] at hm
      omega
    obtain ⟨hc,hR⟩ := hchoice m hmK
    have hzfree : z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8) := by
      simpa only [hc,hR] using hz
    exact norm_deletedPsi_gapRegularFactor_weighted_le
      hp hp1 n m (Ne.symm hmn) a ψ B (Real.pi/8)
        (by nlinarith [Real.pi_pos]) z hzfree (hB m z hz)

end NLS.ZakharovShabat
