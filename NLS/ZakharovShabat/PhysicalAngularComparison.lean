import NLS.ZakharovShabat.PhysicalDirichletPaths
import NLS.ZakharovShabat.PhysicalPsiFamily

/-! # Comparison and construction of physical angular integrals

Every original family identifies the literal physical integrals. One
constructed smooth path makes all off-diagonal integrands integrable;
at open gaps the diagonal integrand and its model are integrable too.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical unitInterval
namespace NLS.ZakharovShabat

namespace SourceSection14OriginalData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  (D : SourceSection14OriginalData (by simp) (by norm_num) W₀ W V s)
include D

/-- The physical and source numerators give identical quotients on any continued root. -/
theorem physicalAngularIntegrand_eq_source (n : ℤ) (u : physicalRealSubmodule)
    (q : ℂ → ℂ) (z : ℂ) :
    physicalAngularIntegrand n u q z =
      sourceAngularIntegrand n s (fun t => q t.1) (z,sourcePhysicalL2Equiv.symm u.val) := by
  rw [physicalAngularIntegrand,D.physicalPsiFunction_eq_family]
  rfl

/-- The literal physical integral equals the source integral on the same path and sheet. -/
theorem physicalAngularPathIntegral_eq_source (n : ℤ) (u : physicalRealSubmodule)
    (q : ℂ → ℂ) {a b : ℂ} (γ : Path a b) :
    physicalAngularPathIntegral n u q γ =
      sourceAngularPathIntegral n s (fun t => q t.1) (sourcePhysicalL2Equiv.symm u.val) γ := by
  rw [physicalAngularPathIntegral,funext (D.physicalAngularIntegrand_eq_source n u q)]
  rfl

/-- Every independent physical off-diagonal integral computes the original beta value. -/
theorem physicalBeta_pathIntegral (n m : ℤ) (hm : m ≠ n) (u : physicalRealSubmodule)
    (C : PhysicalSpectralCircle u.val m)
    (hμ : physicalBoundaryRoots .dirichlet u.val m ∈ ball (C.center:ℂ) C.radius)
    (q : ℂ → ℂ)
    (γ : Path (physicalPeriodicLeft u.val m) (physicalBoundaryRoots .dirichlet u.val m))
    (hq : PhysicalAngularPathRootData u.val m (C.center:ℂ) C.radius q γ)
    (hnorm : l2AntiDiscriminant u.val (physicalBoundaryRoots .dirichlet u.val m) ≠ 0 →
      q (physicalBoundaryRoots .dirichlet u.val m) = l2AntiDiscriminant u.val (physicalBoundaryRoots .dirichlet u.val m))
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1))
    (hi : CurveIntegrable (holomorphicOneForm (physicalAngularIntegrand n u q)) γ) :
    physicalAngularPathIntegral n u q γ =
      sourceAngularBeta (by simp) (by norm_num) n m s (sourcePhysicalL2Equiv.symm u.val) := by
  let φ := sourcePhysicalL2Equiv.symm u.val
  have ha := congrFun (physicalPeriodicEndpoints_eq_source u.val).1 m
  have hb := congrFun (physicalBoundaryRoots_eq_source .dirichlet u.val) m
  let κ := γ.cast ha.symm hb.symm
  have hq' : SourceAngularAdmissiblePathRootData (by simp) (by norm_num) m φ (C.center:ℂ) C.radius
      (fun t => q t.1) κ :=
    ⟨hq.toSource.continuous_root,hq.toSource.square_root,hq.toSource.interior⟩
  have hμ' := hμ
  rw [physicalBoundaryRoots_eq_source] at hμ'
  have hn : sourceAntiDiscriminantCandidate (by simp) (by norm_num) φ
      (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m) ≠ 0 →
      q (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m) =
        sourceAntiDiscriminantCandidate (by simp) (by norm_num) φ
          (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ m) := by
    simpa only [φ,physicalBoundaryRoots_eq_source,physicalAngularTerminal_eq] using hnorm
  have hi' : CurveIntegrable (holomorphicOneForm (fun z => sourceAngularIntegrand n s
      (fun t => q t.1) (z,φ))) κ := by
    have hiκ := hi.cast ha.symm hb.symm
    rw [funext (D.physicalAngularIntegrand_eq_source n u q)] at hiκ
    exact hiκ
  have h := D.previous.beta_original_pathIntegral_eq_value φ
    (D.complex.source_subset (D.complex.real_subset u.property)) n m hm C.toSource hμ'
    (fun t => q t.1) κ hq' hn hγ hi'
  rw [D.physicalAngularPathIntegral_eq_source]
  simpa only [sourceAngularPathIntegral,κ,curveIntegral_cast] using h

/-- Any physical off-diagonal value agrees with the source beta, independently of the path data. -/
theorem physicalAngularIntegralValues_beta (n m : ℤ) (hm : m ≠ n) (u : physicalRealSubmodule)
    {v : ℂ} (hv : v ∈ physicalAngularIntegralValues n m u) :
    v = sourceAngularBeta (by simp) (by norm_num) n m s (sourcePhysicalL2Equiv.symm u.val) := by
  obtain ⟨P,hi,_,rfl⟩ := hv
  exact D.physicalBeta_pathIntegral n m hm u P.circle P.terminal_mem P.root P.path
    P.admissible P.normalized P.smooth hi

/-- A single physical path supplies all off-diagonal integrals and, at an open gap, the eta model. -/
theorem exists_physicalDirichlet_integrablePath (m : ℤ) (u : physicalRealSubmodule) :
    ∃ P : PhysicalDirichletPathData m u,
      (∀ n : ℤ, m ≠ n → CurveIntegrable (holomorphicOneForm (physicalAngularIntegrand n u P.root)) P.path) ∧
      (physicalPeriodicLeft u.val m ≠ physicalPeriodicRight u.val m →
        CurveIntegrable (holomorphicOneForm (physicalAngularIntegrand m u P.root)) P.path ∧
        CurveIntegrable (holomorphicOneForm (physicalEtaModelIntegrand m u.val P.root)) P.path) := by
  let φ := sourcePhysicalL2Equiv.symm u.val
  obtain ⟨C,hμ⟩ := exists_physicalSpectralCircle_dirichlet u m
  have hμ' := hμ
  rw [physicalBoundaryRoots_eq_source] at hμ'
  obtain ⟨Q,γ,hQ,hγ,hnorm,hint,hmodel⟩ := D.previous.original_dirichlet_integral_path φ
    (D.complex.source_subset (D.complex.real_subset u.property)) m C.toSource hμ'
  have ha := congrFun (physicalPeriodicEndpoints_eq_source u.val).1 m
  have hb := congrFun (physicalBoundaryRoots_eq_source .dirichlet u.val) m
  let q : ℂ → ℂ := fun z => Q (z,φ)
  let κ := γ.cast ha hb
  have hq : PhysicalAngularPathRootData u.val m (C.center:ℂ) C.radius q κ :=
    ⟨hQ.continuous_root,fun t ht => (hQ.square_root t ht).trans (physicalAngularRadicand_eq u.val _),
      by simpa only [φ,κ,Path.extend_cast,PhysicalSpectralCircle.toSource,physicalPeriodicSegment_eq_source] using hQ.interior⟩
  have hn : q (physicalBoundaryRoots .dirichlet u.val m) =
      l2AntiDiscriminant u.val (physicalBoundaryRoots .dirichlet u.val m) := by
    simpa only [q,φ,physicalBoundaryRoots_eq_source,physicalAngularTerminal_eq] using hnorm
  let P : PhysicalDirichletPathData m u := ⟨C,hμ,q,κ,hq,hγ,fun _ => hn⟩
  refine ⟨P,?_,?_⟩
  · intro n hmn
    have hi := (hint n hmn).1.cast ha hb
    have he (z : ℂ) : physicalAngularIntegrand n u q z = sourceAngularIntegrand n s Q (z,φ) := by
      rw [physicalAngularIntegrand,D.physicalPsiFunction_eq_family]
      rfl
    change CurveIntegrable (holomorphicOneForm (physicalAngularIntegrand n u q)) κ
    rw [funext he]
    exact hi
  · intro hgap
    have hg : canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ) (periodOnePotential_mem φ) m ≠
        canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ) (periodOnePotential_mem φ) m := by
      simpa only [(physicalPeriodicEndpoints_eq_source u.val).1,(physicalPeriodicEndpoints_eq_source u.val).2] using hgap
    obtain ⟨hi,hm⟩ := hmodel hg
    constructor
    · have he (z : ℂ) : physicalAngularIntegrand m u q z = sourceAngularIntegrand m s Q (z,φ) := by
        rw [physicalAngularIntegrand,D.physicalPsiFunction_eq_family]
        rfl
      change CurveIntegrable (holomorphicOneForm (physicalAngularIntegrand m u q)) κ
      rw [funext he]
      exact hi.cast ha hb
    · have he (z : ℂ) : physicalEtaModelIntegrand m u.val q z =
          sourceAngularEtaPathModelIntegrand (by simp) (by norm_num) m φ Q z := by
        rw [physicalEtaModelIntegrand,physicalOmittedRootProduct_eq_source]
        rfl
      change CurveIntegrable (holomorphicOneForm (physicalEtaModelIntegrand m u.val q)) κ
      rw [funext he]
      exact hm.cast ha hb

/-- Every physical off-diagonal angular integral has one unique value. -/
theorem existsUnique_physicalBeta_value (n m : ℤ) (hm : m ≠ n) (u : physicalRealSubmodule) :
    ∃! v : ℂ, v ∈ physicalAngularIntegralValues n m u := by
  obtain ⟨P,hi,_⟩ := D.exists_physicalDirichlet_integrablePath m u
  refine ⟨physicalAngularPathIntegral n u P.root P.path,⟨P,hi n hm,?_,rfl⟩,?_⟩
  · exact fun h => (hm h.symm).elim
  · intro v hv
    exact (D.physicalAngularIntegralValues_beta n m hm u hv).trans
      (D.physicalBeta_pathIntegral n m hm u P.circle P.terminal_mem P.root P.path
        P.admissible P.normalized P.smooth (hi n hm)).symm

/-- Every physical diagonal value is an original normalized eta integral. -/
theorem physicalEta_value_toSource (m : ℤ) (u : physicalRealSubmodule)
    {v : ℂ} (hv : v ∈ physicalAngularIntegralValues m m u) :
    v ∈ sourceAngularOriginalEtaIntegralValues (by simp) (by norm_num) m s (sourcePhysicalL2Equiv.symm u.val) := by
  obtain ⟨P,hi,hm,he⟩ := hv
  let φ := sourcePhysicalL2Equiv.symm u.val
  have ha := congrFun (physicalPeriodicEndpoints_eq_source u.val).1 m
  have hb := congrFun (physicalBoundaryRoots_eq_source .dirichlet u.val) m
  let κ := P.path.cast ha.symm hb.symm
  have hq : SourceAngularAdmissiblePathRootData (by simp) (by norm_num) m φ
      (P.circle.center:ℂ) P.circle.radius (fun t => P.root t.1) κ :=
    ⟨P.admissible.toSource.continuous_root,P.admissible.toSource.square_root,P.admissible.toSource.interior⟩
  refine ⟨P.circle.toSource,?_,(fun t => P.root t.1),κ,hq,P.smooth,?_,?_,?_,?_⟩
  · simpa only [PhysicalSpectralCircle.toSource,physicalBoundaryRoots_eq_source] using P.terminal_mem
  · simpa only [φ,physicalBoundaryRoots_eq_source,physicalAngularTerminal_eq] using P.normalized
  · have hiκ := hi.cast ha.symm hb.symm
    rw [funext (D.physicalAngularIntegrand_eq_source m u P.root)] at hiκ
    exact hiκ
  · have hmκ := (hm rfl).cast ha.symm hb.symm
    have heq (z : ℂ) : physicalEtaModelIntegrand m u.val P.root z =
        sourceAngularEtaPathModelIntegrand (by simp) (by norm_num) m φ (fun t => P.root t.1) z := by
      rw [physicalEtaModelIntegrand,physicalOmittedRootProduct_eq_source]
      rfl
    rw [funext heq] at hmκ
    exact hmκ
  · rw [D.physicalAngularPathIntegral_eq_source] at he
    simpa only [sourceAngularPathIntegral,κ,curveIntegral_cast] using he

/-- Physical eta choices differ by an integer multiple of 2pi. -/
theorem physicalEta_values_period (m : ℤ) (u : physicalRealSubmodule)
    (hg : physicalPeriodicLeft u.val m ≠ physicalPeriodicRight u.val m)
    {v w : ℂ} (hv : v ∈ physicalAngularIntegralValues m m u)
    (hw : w ∈ physicalAngularIntegralValues m m u) : ∃ k : ℤ, v-w = (k:ℂ)*(2*Real.pi) := by
  have hg' : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sourcePhysicalL2Equiv.symm u.val)) (periodOnePotential_mem _) m ≠ 0 := by
    rw [canonicalPeriodicGap,sub_ne_zero]
    simpa only [(physicalPeriodicEndpoints_eq_source u.val).1,(physicalPeriodicEndpoints_eq_source u.val).2] using hg.symm
  exact D.previous.eta_original_integral_values_period (sourcePhysicalL2Equiv.symm u.val)
    (D.complex.source_subset (D.complex.real_subset u.property)) m hg'
    (D.physicalEta_value_toSource m u hv) (D.physicalEta_value_toSource m u hw)

/-- Every real open physical gap has an integrable normalized eta path. -/
theorem physicalEta_values_nonempty (m : ℤ) (u : physicalRealSubmodule)
    (hg : physicalPeriodicLeft u.val m ≠ physicalPeriodicRight u.val m) :
    (physicalAngularIntegralValues m m u).Nonempty := by
  obtain ⟨P,_,hi⟩ := D.exists_physicalDirichlet_integrablePath m u
  exact ⟨_,P,(hi hg).1,fun _ => (hi hg).2,rfl⟩

end SourceSection14OriginalData

end NLS.ZakharovShabat
