import NLS.Dynamics.HamiltonianPhaseObstruction
import NLS.ZakharovShabat.SourceOrdinarySourceObstruction
import NLS.ZakharovShabat.SourceHamiltonianOrdinaryFlow

/-! # Forward-time nonextension with the physical Hamiltonian signs

The finite-gap physical first coordinate rotates with negative phase.
Its unbounded frequency still prevents convergence on `[0,T]`. This gives
the source obstruction with the time orientation of the actual NLS PDE.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p}
namespace SourceAbelianMomentAtlas
variable {W P : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {W₂ P₂ : Set (CoeffPair 2)} {s₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable {V₂ B₂ X₂ : Set (CoeffPair 2)} {t₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The observed finite-gap Hilbert flow has the negative physical phase
at arbitrary real time and in any larger target exponent. -/
theorem complex_map_hilbertHamiltonianFlow_fst (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P s)
    (H : SourceAbelianMomentAtlas (by simp) (by norm_num) W₂ s₂)
    (hs₂ : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P₂ s₂)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₂ B₂ X₂ t₂)
    {V B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    {hq : q ≠ ⊤} {hq1 : 1 < q} {Vq Bq Xq : Set (CoeffPair q)}
    {tq : (n : ℤ) → CoeffPair q → DeletedCoeff q n}
    (Q : SourceBirkhoffMapComplexData hq hq1 Vq Bq Xq tq)
    (h2p : 2 ≤ p) (h2q : 2 ≤ q)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) (time : ℝ) :
    (sourceComplexBirkhoffMap hq hq1 tq
      (realTypeSourceExponentInclusion h2q
        (H.hamiltonianOrdinarySourceFlow E le_rfl (sourceFiniteGapHilbertModel hp hp1 φ hf) time)).val).1 n =
      Complex.exp (((-time*A.finiteGapOrdinaryFrequency φ hf n : ℝ) : ℂ)*Complex.I)*
        (sourceComplexBirkhoffMap hp hp1 t φ.val).1 n := by
  rw [← E.complex_map_exponent Q h2q,H.complex_map_hamiltonianOrdinarySourceFlow]
  change (Birkhoff.hamiltonianPhaseFlow (H.ordinaryPhaseFrequency le_rfl
    (sourceFiniteGapHilbertModel hp hp1 φ hf)) time
    (sourceComplexBirkhoffMap (by simp) (by norm_num) t₂ (sourceFiniteGapHilbertModel hp hp1 φ hf).val)).1 n = _
  rw [Birkhoff.hamiltonianPhaseFlow_fst,← A.finiteGapOrdinaryFrequency_hilbertModel hs H hs₂ E]
  congr 1
  have he := congrArg (fun z : Coeff p × Coeff p => z.1 n)
    (E.complex_map_exponent D h2p (sourceFiniteGapHilbertModel hp hp1 φ hf))
  change _ = (sourceComplexBirkhoffMap hp hp1 t
    (realTypeSourceExponentInclusion h2p (sourceFiniteGapHilbertModel hp hp1 φ hf) : realTypeSourceSubmodule p).val).1 n at he
  rw [sourceFiniteGapHilbertModel_inclusion] at he
  exact he

/-- Even agreement only on finite-gap classical sources rules out continuity
on the forward interval `[0,T]`, with the physical Hamiltonian orientation. -/
theorem not_continuousAt_hamiltonianSource_extension (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 P s) (hP : IsOpen P)
    (hr : realTypeSourceLocus p ⊆ P)
    {V B X : Set (CoeffPair p)} {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (D : SourceBirkhoffMapComplexData hp hp1 V B X t)
    (H : SourceAbelianMomentAtlas (by simp) (by norm_num) W₂ s₂)
    (hs₂ : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P₂ s₂)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₂ B₂ X₂ t₂)
    {hq : q ≠ ⊤} {hq1 : 1 < q} {Vq Bq Xq : Set (CoeffPair q)}
    {tq : (n : ℤ) → CoeffPair q → DeletedCoeff q n}
    (Q : SourceBirkhoffMapComplexData hq hq1 Vq Bq Xq tq)
    (h2p : 2 ≤ p) (h2q : 2 ≤ q) (T : ℝ) (hT : 0 < T)
    (φ : realTypeSourceSubmodule p) (hφ : φ ∉ sourceHilbertLocus h2p)
    (F : realTypeSourceSubmodule p → C(Icc (0 : ℝ) T,realTypeSourceSubmodule q))
    (he : ∀ ψ : realTypeSourceSubmodule p, ∀ hf : ψ ∈ sourceFiniteGapLocus hp hp1,
      ∀ time : Icc (0 : ℝ) T, F ψ time = realTypeSourceExponentInclusion h2q
        (H.hamiltonianOrdinarySourceFlow E le_rfl (sourceFiniteGapHilbertModel hp hp1 ψ hf) time.val)) :
    ¬ ContinuousAt F φ := by
  intro hF
  have hne : φ ≠ 0 := by
    intro hz
    apply hφ
    rw [hz,mem_sourceHilbertLocus_iff]
    simp
  obtain ⟨n,hn⟩ := D.exists_complex_map_fst_ne_zero φ hne
  obtain ⟨ψ,hf,hψ⟩ := exists_sourceFiniteGap_sequence hp hp1 φ
  let c : C(realTypeSourceSubmodule q,ℂ) :=
    ⟨fun χ => (sourceComplexBirkhoffMap hq hq1 tq χ.val).1 n,
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) q n).continuous.comp Q.continuous_complex_map_real.fst⟩
  have hamp : Tendsto (fun j => (sourceComplexBirkhoffMap hp hp1 t (ψ j).val).1 n) atTop
      (𝓝 ((sourceComplexBirkhoffMap hp hp1 t φ.val).1 n)) :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.comp D.continuous_complex_map_real.fst).continuousAt.tendsto.comp hψ
  apply NLS.Dynamics.not_tendsto_hamiltonian_phase_trajectories T hT
    (fun j => A.finiteGapOrdinaryFrequency (ψ j) (hf j) n)
    (fun j => (sourceComplexBirkhoffMap hp hp1 t (ψ j).val).1 n) _ hn
    (A.tendsto_finiteGapOrdinaryFrequency_atTop hs hP hr h2p φ hφ ψ hf hψ n) hamp
    (fun j => c.comp (F (ψ j))) (fun j time => ?_) (c.comp (F φ))
    (((ContinuousMap.continuous_postcomp c).continuousAt.comp hF).tendsto.comp hψ)
  change (sourceComplexBirkhoffMap hq hq1 tq (F (ψ j) time).val).1 n = _
  rw [he (ψ j) (hf j) time]
  exact A.complex_map_hilbertHamiltonianFlow_fst hs.toSourcePsiIsolatingComplexExtension
    H hs₂ E D Q h2p h2q (ψ j) (hf j) n time.val

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
