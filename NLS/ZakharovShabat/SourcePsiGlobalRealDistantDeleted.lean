import NLS.ZakharovShabat.SourcePsiRealCenteredShiftedDisc
import NLS.ZakharovShabat.SourcePsiGlobalContourFamily

/-!
# Real psi coordinates for distant deleted indices

The finitely many shifted head circles have one lattice-separation
cutoff. Beyond it, every selected circle supports the real open-gap
or collapsed-gap argument on one common source neighborhood. The
free-centered tail circles satisfy the same separation automatically.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Near a real-type source, all selected psi equation coordinates are
real on the real locus whenever the deleted index is sufficiently far
out. The contour family is real-centered and independent of that
deleted index. -/
theorem exists_local_sourcePsi_realCoordinates_of_distantDeleted
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        (∀ m : ℤ, (c m).im = 0) ∧
        (∀ m : ℤ, K < m.natAbs →
          c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
        (∀ ψ ∈ V, ∀ m : ℤ,
          0 < R m ∧
          sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (R m) ∧
          closedBall (c m) (R m) ⊆
            sourceStandardRootOmittedDomain hp hp1 ψ m ∧
          sphere (c m) (R m) ⊆
            sourceCanonicalRootDomain hp hp1 ψ) ∧
        ∀ ψ ∈ V, IsRealType (CoeffPair.toMax p ψ) →
          ∀ n : ℤ, N ≤ n.natAbs →
            ∀ a : DeletedCoeff p n,
              (∀ k : ℤ, (displacedRoots (a : Coeff p) k).im = 0) →
                ∀ m : ℤ,
                  (sourcePsiEquationCoordinate hp hp1 n m
                    (a : Coeff p) ψ (c m) (R m)).im = 0 := by
  obtain ⟨K,Vgeom,hVgeomOpen,hφVgeom,c,R,hcReal,hchoice,hgeom⟩ :=
    exists_local_sourcePsi_allGap_realCenteredContourFamily hp hp1 φ hφ
  obtain ⟨W,hWopen,_,hrealW,hQ⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  have hRhead (m : ℤ) (hm : m ∈ s) : 0 ≤ R m :=
    (hgeom φ hφVgeom m).1.le
  obtain ⟨L,hL⟩ := exists_uniform_shifted_disc_lattice_cutoff
    s c R hRhead
  let N : ℕ := K+L+1
  let V : Set (CoeffPair p) := Vgeom ∩ W
  have hVopen : IsOpen V := hVgeomOpen.inter hWopen
  have hφV : φ ∈ V := ⟨hφVgeom,hrealW hφ⟩
  refine ⟨N,K,V,hVopen,hφV,c,R,hcReal,hchoice,?_,?_⟩
  · intro ψ hψ m
    exact hgeom ψ hψ.1 m
  intro ψ hψ hreal n hn a hroots m
  by_cases hmn : n = m
  · subst m
    simp [sourcePsiEquationCoordinate]
  have hneq : n ≠ m := hmn
  have hsep : 2*(‖c m-(Real.pi : ℂ)*m‖+R m) ≤
      Real.pi*|((n-m : ℤ) : ℝ)| := by
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
      exact hL m hm n hdist
    · have hmK : K < m.natAbs := by
        simp only [s,Finset.mem_Icc] at hm
        omega
      obtain ⟨hc,hR⟩ := hchoice m hmK
      have hd : 1 ≤ |((n-m : ℤ) : ℝ)| := by
        have h := Int.one_le_abs (sub_ne_zero.mpr hneq)
        exact_mod_cast h
      rw [hc,hR]
      simp only [sub_self,norm_zero,zero_add]
      nlinarith [Real.pi_pos]
  let x : ℝ := (c m).re
  have hx : (x:ℂ) = c m := by
    apply Complex.ext
    · rfl
    · simpa [x] using (hcReal m).symm
  obtain ⟨hR,hseg,hdom,hcircle⟩ := hgeom ψ hψ.1 m
  have hψW : ψ ∈ W := hψ.2
  have hcoord :=
    sourcePsiEquationCoordinate_realCentered_im_eq_zero_of_shiftedRealGap
      hp hp1 ψ hreal n m hneq a hroots x (R m) hR
      (by simpa only [hx] using hseg)
      (by simpa only [hx] using hdom)
      (by simpa only [hx] using hcircle)
      (by simpa only [hx] using hsep)
      W hψW (hQ m).2
  simpa only [hx] using hcoord

end NLS.ZakharovShabat
