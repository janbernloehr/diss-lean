import NLS.ZakharovShabat.SourcePsiGlobalHeadCoordinateBound
import NLS.ZakharovShabat.SourcePsiGlobalTailSequenceBound

/-!
# A locally uniformly bounded global psi equation sequence

The finite selected head is patched to the free-centered tail. The
result is a deleted `ℓᵖ` sequence on one contour family near every
real-type source, with a norm bound independent of the deleted index.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Near an arbitrary real-type source and root input, all coordinates
of the global psi contour equation form a deleted `ℓᵖ` sequence. The
sequence norm has one local bound for every deleted index. -/
theorem exists_local_sourcePsi_globalEquation_uniformNorm
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ K : ℕ, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
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
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ n : ℤ, ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
            ((a : Coeff p),ψ) ∈ U →
              ∃ F : DeletedCoeff p n,
                (∀ m : ℤ, (F : Coeff p) m =
                  sourcePsiEquationCoordinate hp hp1 n m
                    (a : Coeff p) ψ (c m) (R m)) ∧
                ‖F‖ ≤ C := by
  obtain ⟨Utail,hUtailOpen,hbaseTail,Ktail,Ctail,hCtail,htail⟩ :=
    exists_local_sourcePsi_tailEquation_uniformNorm hp hp1 φ hφ a₀
  obtain ⟨Uhead,hUheadOpen,hbaseHead,K,hKtail,c,R,hcReal,hchoice,hgeom,
      ⟨Niso,εiso,hcluster,hdisjoint,hfilled⟩,Chead,hChead,hhead⟩ :=
    exists_local_sourcePsi_uniformHeadCoordinateBound
      hp hp1 φ hφ a₀ Ktail
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let U : Set (Coeff p × CoeffPair p) := Utail ∩ Uhead
  have hUopen : IsOpen U := hUtailOpen.inter hUheadOpen
  have hbase : (a₀,φ) ∈ U := ⟨hbaseTail,hbaseHead⟩
  let C : ℝ := s.card*Chead+Ctail
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨U,hUopen,hbase,K,c,R,hcReal,hchoice,?_,
    ⟨Niso,εiso,?_,hdisjoint,hfilled⟩,C,hC,?_⟩
  · intro t ht m
    exact hgeom t ht.2 m
  · intro t ht m
    exact hcluster t ht.2 m
  intro n a ψ hpair
  obtain ⟨Ftail,hFtail,hFtailNorm⟩ := htail n a ψ hpair.1
  let Fraw : ℤ → ℂ := fun m =>
    sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ (c m) (R m)
  have hout (m : ℤ) (hm : m ∉ s) :
      Fraw m = (Ftail : Coeff p) m := by
    have hmK : K < m.natAbs := by
      simp only [s,Finset.mem_Icc] at hm
      omega
    have hmTail : Ktail ≤ m.natAbs := by omega
    obtain ⟨hc,hR⟩ := hchoice m hmK
    have htailEq : (Ftail : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m (a : Coeff p) ψ
          ((Real.pi : ℂ)*m) (Real.pi/8) := by
      simpa only [if_pos hmTail] using hFtail m
    simp only [Fraw,hc,hR]
    exact htailEq.symm
  have hmem : Memℓp Fraw p := by
    apply NLS.memℓp_of_eq_outside_finset
      (lp.memℓp (Ftail : Coeff p)) s
    exact hout
  let Fcoeff : Coeff p := ⟨Fraw,hmem⟩
  have hFn : Fcoeff n = 0 := by
    simp [Fcoeff,Fraw,sourcePsiEquationCoordinate]
  let F : DeletedCoeff p n := ⟨Fcoeff,hFn⟩
  refine ⟨F,fun m => rfl,?_⟩
  have hFhead (m : ℤ) (hm : m ∈ s) : ‖Fcoeff m‖ ≤ Chead := by
    have hmK : m.natAbs ≤ K := by
      simp only [s,Finset.mem_Icc] at hm
      omega
    exact hhead n a ψ hpair.2 m hmK
  have hFout (m : ℤ) (hm : m ∉ s) :
      Fcoeff m = (Ftail : Coeff p) m := hout m hm
  have hFbound : ‖Fcoeff‖ ≤ s.card*Chead+‖Ftail‖ :=
    NLS.Coeff.norm_le_of_eq_outside_finset
      Fcoeff (Ftail : Coeff p) s Chead hFhead hFout
  change ‖Fcoeff‖ ≤ C
  calc
    ‖Fcoeff‖ ≤ s.card*Chead+‖Ftail‖ := hFbound
    _ ≤ s.card*Chead+Ctail := by gcongr
    _ = C := rfl

end NLS.ZakharovShabat
