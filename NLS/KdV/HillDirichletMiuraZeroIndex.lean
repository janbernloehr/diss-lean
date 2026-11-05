import NLS.KdV.HillHminusOneDirichletMiuraSource
import NLS.ZakharovShabat.SourceBoundaryDisplacementAnalytic

/-! # The added zero-frequency root has canonical NLS index zero

The exact source characteristic has a root at zero for every rotated
Miura source. Strict ordering, continuity and exhaustion keep that root
at index zero along the real scalar homotopy. Positive indices therefore
give exactly positive frequencies, including all central indices.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV

theorem canonicalDirichletMiuraRoot_zero_index (u : Coeff 2)
    (hu : ∀ k : ℤ, u (-k) = conj (u k)) :
    canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet (hillDirichletMiuraSource u) 0 = 0 := by
  let L : ℝ → CoeffPair 2 := fun t => hillDirichletMiuraSource ((t : ℂ) • u)
  have hL : Continuous L := hillDirichletMiuraSource.continuous.comp
    (Complex.continuous_ofReal.smul continuous_const)
  have hreal (t : ℝ) : IsRealType (CoeffPair.toMax 2 (L t)) := by
    apply hillDirichletMiuraSource_real
    intro k
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,hu,map_mul,conj_ofReal]
  let a : ℤ → ℝ → ℂ := fun n t => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet (L t) n
  have ha (n : ℤ) : Continuous (a n) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp (g := fun p : CoeffPair 2 =>
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet p n) (f := L)
      (continuousAt_canonicalPeriodOneBoundaryRoots_of_realType (by simp) (by norm_num) .dirichlet (L t) (hreal t) n)
      hL.continuousAt
  have hmono (t : ℝ) : StrictMono (fun n : ℤ => (a n t).re) :=
    strictMono_canonicalPeriodOneBoundaryRoots_re_of_realType (by simp) (by norm_num) .dirichlet (L t) (hreal t)
  have hex (t : ℝ) : ∃ n : ℤ, a n t = 0 := by
    apply (canonicalPeriodOneBoundaryRoots_exhaustive (by simp) (by norm_num) .dirichlet (L t) 0).mp
    apply (periodOneBoundaryCharacteristic_eq_zero_iff (by simp) (by norm_num) .dirichlet (L t) 0).mp
    exact periodOneBoundaryCharacteristic_dirichletMiura_zero _
  have hc : IsClopen {t : ℝ | a 0 t = 0} := by
    refine ⟨isClosed_eq (ha 0) continuous_const,?_⟩
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    change a 0 t = 0 at ht
    have hl : (a (-1) t).re < 0 := by
      have hh := hmono t (by norm_num : (-1 : ℤ) < 0)
      dsimp only at hh
      rwa [ht,zero_re] at hh
    have hr : 0 < (a 1 t).re := by
      have hh := hmono t (by norm_num : (0 : ℤ) < 1)
      dsimp only at hh
      rwa [ht,zero_re] at hh
    have hleft := ((Complex.continuous_re.comp (ha (-1))).continuousAt).eventually_lt_const hl
    have hright := ((Complex.continuous_re.comp (ha 1)).continuousAt).eventually_const_lt hr
    filter_upwards [hleft,hright] with s hsL hsR
    obtain ⟨m,hm⟩ := hex s
    have hml : (-1 : ℤ) < m := (hmono s).lt_iff_lt.mp (by rw [hm,zero_re]; exact hsL)
    have hmr : m < (1 : ℤ) := (hmono s).lt_iff_lt.mp (by rw [hm,zero_re]; exact hsR)
    have hm0 : m = 0 := by omega
    rwa [hm0] at hm
  have h0 : (0 : ℝ) ∈ {t : ℝ | a 0 t = 0} := by
    simp [a,L,canonicalPeriodOneBoundaryRoots_zero]
  have hall := hc.eq_univ ⟨0,h0⟩
  have h1 : (1 : ℝ) ∈ {t : ℝ | a 0 t = 0} := by rw [hall]; trivial
  simpa only [mem_ofPred_eq,a,L,ofReal_one,one_smul] using h1

theorem canonicalDirichletMiuraRoot_re_pos_iff (u : Coeff 2)
    (hu : ∀ k : ℤ, u (-k) = conj (u k)) (n : ℤ) :
    0 < (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet (hillDirichletMiuraSource u) n).re ↔ 0 < n := by
  have hm := strictMono_canonicalPeriodOneBoundaryRoots_re_of_realType
    (by simp) (by norm_num) .dirichlet (hillDirichletMiuraSource u) (hillDirichletMiuraSource_real u hu)
  have h := hm.lt_iff_lt (a := 0) (b := n)
  rwa [canonicalDirichletMiuraRoot_zero_index u hu,zero_re] at h

end NLS.KdV
