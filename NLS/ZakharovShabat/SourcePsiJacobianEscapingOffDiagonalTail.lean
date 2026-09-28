import NLS.ZakharovShabat.SourcePsiJacobianUniformOffDiagonalTail
import NLS.ZakharovShabat.SourcePsiJacobianOffDiagonalRowMajorant
import NLS.ZakharovShabat.SourcePsiGapProductCompact
import NLS.SequenceSpaces.DeletedCoordinateAtInfinity
import NLS.ZakharovShabat.SourcePsiCommonJacobianCharts

/-!
# A common off-diagonal bound for escaping deleted indices

For a fixed gap-contained root sequence, deleting an index that tends
to infinity remains eventually inside any neighborhood of the full
sequence. The locally uniform scalar Jacobian estimate therefore
applies simultaneously to all sufficiently distant deleted indices.
Its varying quotient majorants are dominated by one fixed `ℓᵖ` row
majorant.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The free-circle off-diagonal scalar Jacobians at deleted copies of
a gap-contained root sequence have one reciprocal entry bound on all
distant rows and columns, uniformly as the deleted index escapes. -/
theorem exists_sourcePsi_escaping_offDiagonal_scalarEntryMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ) :
    ∃ Krow Kcol : ℕ, ∃ b : Coeff p,
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ∀ m : ℤ, Krow ≤ m.natAbs → m ≠ n →
          ∀ k : ℤ, Kcol ≤ k.natAbs → ∀ hkn : k ≠ n, m ≠ k →
            ‖deriv (fun t : ℂ =>
              sourcePsiDeletedEquationCoordinate hp hp1 n m
                (Coeff.deleteCoordinateTo n a +
                  Coeff.deletedSingleCLM n k hkn t) φ
                ((Real.pi : ℂ)*m) (Real.pi/8)) 0‖ ≤
              ‖b m‖ / ‖((m-k : ℤ) : ℂ)‖ := by
  obtain ⟨U,hUopen,hbase,Krow,M,hM,htail⟩ :=
    exists_local_sourcePsi_offDiagonalJacobian_uniformTail_tailColumns
      hp hp1 φ hφ a
  obtain ⟨Kcol,hKcol⟩ :=
    Coeff.exists_cutoff_norm_apply_lt hp a
      (by positivity : (0 : ℝ) < Real.pi/4)
  let b : Coeff p := sourcePsiOffDiagonalUniformRowMajorant hp hp1 a φ M
  have hparam : Tendsto
      (fun n : ℤ => (Coeff.deleteCoordinate n a,φ))
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 (a,φ)) := by
    simpa only [nhds_prod_eq] using
      (Coeff.tendsto_deleteCoordinate_at_natAbs hp a).prodMk
        (tendsto_const_nhds (x := φ))
  have hnear : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      (Coeff.deleteCoordinate n a,φ) ∈ U :=
    hparam.eventually (hUopen.mem_nhds hbase)
  refine ⟨Krow,Kcol,b,?_⟩
  filter_upwards [hnear] with n hn
  let aₙ : DeletedCoeff p n := Coeff.deleteCoordinateTo n a
  have hpair : ((aₙ : Coeff p),φ) ∈ U := hn
  have hdel : (aₙ : Coeff p) n = 0 := by
    change Coeff.deleteCoordinate n a n = 0
    exact Coeff.deleteCoordinate_apply_same n a
  have hroots (j : ℤ) : (displacedRoots (aₙ : Coeff p) j).im = 0 := by
    by_cases hj : j = n
    · subst j
      simp [displacedRoots,hdel]
    · have heq : displacedRoots (aₙ : Coeff p) j =
          displacedRoots a j := by
        simp [aₙ,displacedRoots,Coeff.deleteCoordinateTo,
          Coeff.deleteCoordinate_apply_other n j hj]
      rw [heq]
      exact sourcePeriodicSegment_im_eq_zero_of_realType
        hp hp1 φ hφ j _ (ha j)
  have hlocalized (j : ℤ) (hj : Kcol ≤ j.natAbs) :
      ‖(aₙ : Coeff p) j‖ ≤ Real.pi/4 := by
    have hle : ‖(aₙ : Coeff p) j‖ ≤ ‖a j‖ := by
      by_cases hjn : j = n
      · subst j
        simp [hdel]
      · simp [aₙ,Coeff.deleteCoordinateTo,
          Coeff.deleteCoordinate_apply_other n j hjn]
    exact hle.trans (hKcol j hj).le
  obtain ⟨B,hBnorm,hentry⟩ :=
    htail n aₙ φ hpair hφ hroots Kcol hlocalized
  intro m hm hmn k hk hkn hmk
  have hmain := hentry m hm hmn k hk hkn hmk
  have hmajor :
      ‖sourcePsiOffDiagonalRowMajorant hp hp1 (aₙ : Coeff p) φ B m‖ ≤
        ‖b m‖ :=
    norm_sourcePsiOffDiagonalRowMajorant_delete_le_uniform
      hp hp1 a φ B M hM hBnorm n m
  exact hmain.trans (div_le_div_of_nonneg_right hmajor (norm_nonneg _))

/-- One common contour family makes the escaping full Jacobians obey
the same fixed reciprocal off-diagonal matrix bound on distant rows
and columns. The omitted row and column are excluded explicitly. -/
theorem exists_sourcePsi_escaping_fullJacobian_offDiagonalEntryMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      ∃ Krow Kcol : ℕ, ∃ b : Coeff p,
        ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
          ∀ m : ℤ, Krow ≤ m.natAbs → m ≠ n →
            ∀ k : ℤ, Kcol ≤ k.natAbs → k ≠ n → m ≠ k →
              ‖(sourcePsiFullRootJacobian hp hp1 n c R
                (Coeff.deleteCoordinateTo n a) φ
                  (lp.single p k 1)) m‖ ≤
                ‖b m‖ / ‖((m-k : ℤ) : ℂ)‖ := by
  obtain ⟨c,R,_,Kfree,hfree,δ,hδ,C,hC,hcharts⟩ :=
    exists_common_sourcePsi_selectedJacobianCharts_at_natAbs
      hp hp1 a φ hφ
  obtain ⟨Kscalar,Kcol,b,hscalar⟩ :=
    exists_sourcePsi_escaping_offDiagonal_scalarEntryMajorant
      hp hp1 a φ hφ ha
  let Krow := max Kscalar (Kfree+1)
  refine ⟨c,R,Krow,Kcol,b,?_⟩
  filter_upwards [hcharts,hscalar] with n hchart hs
  obtain ⟨U,hUopen,hpair,_,_,hcoord,hdiff⟩ := hchart
  intro m hm hmn k hk hkn hmk
  have hmScalar : Kscalar ≤ m.natAbs := by dsimp [Krow] at hm; omega
  have hmFree : Kfree < m.natAbs := by dsimp [Krow] at hm; omega
  have hentry := sourcePsiFullRootJacobian_retained_entry_eq_deriv
    hp hp1 n c R U hUopen hcoord hdiff
      (Coeff.deleteCoordinateTo n a) φ hpair m k hmn hkn
  rw [hentry, (hfree m hmFree).1, (hfree m hmFree).2]
  exact hs m hmScalar hmn k hk hkn hmk

end NLS.ZakharovShabat
