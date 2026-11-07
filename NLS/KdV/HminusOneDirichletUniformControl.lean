import NLS.KdV.HminusOneDirichletComplexLabels
import NLS.ZakharovShabat.CanonicalBoundaryUniformCutoff

/-! A COMMON original H^-1 neighborhood and cutoff control every actual
complex high Dirichlet label, its algebraic simplicity and its analyticity. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

/-- A complete actual canonical boundary labeling supplies scalar native
control at its OWN cutoff. No pointwise canonical cutoff is used. -/
theorem hillHminusDirichletComplexControl_of_boundaryLabeling
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) (N : ℕ)
    (h : BoundaryRootLabeling .dirichlet (by simp)
      (auxiliaryPeriodOneDirichletPotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
      (auxiliaryPeriodOneDirichletPotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property N
      (canonicalAuxiliaryPeriodOneRoots (by simp) (by norm_num) .dirichlet (hillMiuraDiagonal u))) :
    HillHminusDirichletComplexControl q u c N := by
  have hc := auxiliaryCountingData_of_boundary (by simp)
    (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
    (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property h.counting
  have hd (n : ℕ) (hn : N < n) :
      hillMiuraDiracDirichlet u n ∈ Metric.ball ((Real.pi:ℂ)*n) (Real.pi/4) ∧
      BoundaryCondition.auxiliaryAlgebraicMultiplicity .dirichlet (by simp)
        (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
        (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property
        (hillMiuraDiracDirichlet u n) = 1 := by
    have hs := h.distant_spec (n:ℤ) (by simpa using hn)
    constructor
    · simpa only [hillMiuraDiracDirichlet,Int.cast_natCast] using hs.1
    · rw [BoundaryCondition.auxiliaryAlgebraicMultiplicity_eq]
      exact hs.2
  refine ⟨h.counting.periodic.cutoff_pos,hi,hc,fun n hn => (hd n hn).1,?_⟩
  intro n hn
  have hz : hillMiuraDiracDirichlet u n ≠ 0 := by
    have hp := re_pos_of_mem_positive_frequencyDisk n (by omega)
      (hillMiuraDiracDirichlet u n) (hd n hn).1
    intro he
    rw [he] at hp
    exact (lt_irrefl 0) hp
  rw [hillMiuraDirichletEnergy,
    ← auxiliaryDirichletMultiplicity_eq_native_of_ne_zero q u c _ hi hz]
  exact (hd n hn).2

/-- A common control cutoff identifies the INTRINSIC label with the actual
positive auxiliary branch at the SAME original index, even below the
pointwise cutoff chosen by the canonical construction. -/
theorem hillHminusDirichletComplexLabels_eq_tail_of_control
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ) (N : ℕ)
    (h : HillHminusDirichletComplexControl q u c N) (n : ℕ+) (hn : N < (n:ℕ)) :
    hillHminusDirichletComplexLabels q n = hillMiuraDirichletEnergy u c (n:ℕ) := by
  obtain ⟨mu,hm⟩ := exists_hillHminusDirichletComplexLabeling_of_control q u c N h
  rw [hillHminusDirichletComplexLabels_eq_labeling q u c N mu hm n]
  have hidx : Equiv.pnatEquivNat n+1 = (n:ℕ) := PNat.natPred_add_one n
  rw [hm.distant (Equiv.pnatEquivNat n) (by omega),hidx]

/-- The COMMON high labels have actual native algebraic multiplicity one. -/
theorem hillHminusDirichletComplexLabels_multiplicity_one_of_control
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ) (N : ℕ)
    (h : HillHminusDirichletComplexControl q u c N) (n : ℕ+) (hn : N < (n:ℕ)) :
    singularDirichletAlgebraicMultiplicity (periodOneOriginal q)
      (hillHminusDirichletComplexLabels q n) = 1 := by
  rw [hillHminusDirichletComplexLabels_eq_tail_of_control q u c N h n hn]
  exact h.tail_multiplicity (n:ℕ) hn

/-- Every fixed Miura chart admits ONE original H^-1 neighborhood and cutoff
that control ALL high native labels. EVERY such label is analytic on that
SAME complex neighborhood; no reality or pointwise-cutoff hypothesis remains. -/
theorem HillHminusMiuraChart.exists_uniform_analytic_dirichletControl
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ C.domain ∧
      (∀ a ∈ V, HillHminusDirichletComplexControl a (C.lift a) C.energyShift N) ∧
      ∀ n : ℕ+, N < (n:ℕ) →
        AnalyticOnNhd ℂ (fun a => hillHminusDirichletComplexLabels a n) V := by
  let T := auxiliaryPeriodOneDirichletPotential (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2:ℝ≥0∞))
  let F : PeriodOneHminusOne → dirichletSubspace (p := 2) :=
    fun a => T (hillMiuraDiagonal (C.lift a))
  have hF : AnalyticOnNhd ℂ F C.domain := by
    intro a ha
    exact (T.analyticAt _).comp ((hillMiuraDiagonal.analyticAt _).comp (C.lift_analytic a ha))
  obtain ⟨N,U,hN,hU,_,hqU,_,hl,han⟩ :=
    exists_uniform_analytic_canonical_boundaryRoots (by simp) (by norm_num) (F q)
  let V := C.domain ∩ F ⁻¹' U
  have hV : IsOpen V := hF.continuousOn.isOpen_inter_preimage C.domain_open hU
  have hcontrol (a : PeriodOneHminusOne) (ha : a ∈ V) :
      HillHminusDirichletComplexControl a (C.lift a) C.energyShift N :=
    hillHminusDirichletComplexControl_of_boundaryLabeling a (C.lift a) C.energyShift
      (C.image a ha.1) N (hl (F a) ha.2 .dirichlet)
  refine ⟨N,V,hN,hV,⟨hq,hqU⟩,inter_subset_left,hcontrol,?_⟩
  intro n hn a ha
  have hn' : N < ((n:ℕ):ℤ).natAbs := by simpa using hn
  have hroot := (han .dirichlet ((n:ℕ):ℤ) hn' (F a) ha.2).comp
    (f := F) (hF a ha.1)
  have henergy : AnalyticAt ℂ (fun b => hillMiuraDirichletEnergy (C.lift b) C.energyShift (n:ℕ)) a :=
    (hroot.pow 2).sub analyticAt_const
  apply henergy.congr
  filter_upwards [hV.mem_nhds ha] with b hb
  exact (hillHminusDirichletComplexLabels_eq_tail_of_control b (C.lift b) C.energyShift
    N (hcontrol b hb) n hn).symm

end NLS.KdV
