import NLS.ZakharovShabat.SourcePsiGlobalEquationAnalytic

/-!
# Matrix entries of the selected psi equation derivative

The sequence-valued psi equation agrees coordinatewise with its
selected scalar contour equations on a common open neighborhood.
Consequently, its directional scalar derivatives are exactly those
computed by the contour variation and gap estimates.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The bounded root-direction Jacobian of a selected sequence-valued
psi equation, with the source potential fixed. -/
def sourcePsiSelectedRootJacobian
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) :
    DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
  fderiv ℂ (fun b : DeletedCoeff p n =>
    sourcePsiSelectedEquationSequence hp hp1 n c R b ψ) a

/-- At a point of holomorphy, each matrix entry of the bounded
root-direction Jacobian is the corresponding selected-coordinate
directional derivative. -/
theorem sourcePsiSelectedRootJacobian_entry_eq_deriv
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (hpair : (a,ψ) ∈ U)
    (m k : ℤ) (hkn : k ≠ n) :
    ((sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
      (Coeff.deletedSingleCLM n k hkn 1) : DeletedCoeff p n) : Coeff p) m =
      deriv (fun z : ℂ =>
        (sourcePsiSelectedEquationSequence hp hp1 n c R
          (a+Coeff.deletedSingleCLM n k hkn z) ψ : Coeff p) m) 0 := by
  let F : DeletedCoeff p n → DeletedCoeff p n :=
    fun b => sourcePsiSelectedEquationSequence hp hp1 n c R b ψ
  let L : DeletedCoeff p n →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL)
  let Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
    sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
  have hpairDiff : DifferentiableAt ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2)
      (a,ψ) :=
    (hdiff (a,ψ) hpair).differentiableAt (hUopen.mem_nhds hpair)
  have hinc : DifferentiableAt ℂ
      (fun b : DeletedCoeff p n => (b,ψ)) a := by fun_prop
  have hF : HasFDerivAt F Q a := by
    exact (hpairDiff.comp a hinc).hasFDerivAt
  have hLF : HasFDerivAt (fun b => L (F b)) (L.comp Q) a :=
    L.hasFDerivAt.comp a hF
  have hsingle : HasDerivAt (Coeff.deletedSingleCLM (p := p) n k hkn)
      (Coeff.deletedSingleCLM n k hkn 1) 0 :=
    (Coeff.deletedSingleCLM (p := p) n k hkn).hasDerivAt
  have hline : HasDerivAt
      (fun z : ℂ => a+Coeff.deletedSingleCLM n k hkn z)
      (Coeff.deletedSingleCLM n k hkn 1) 0 := by
    simpa using hsingle.const_add a
  have hcomp := hLF.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
  change (L.comp Q) (Coeff.deletedSingleCLM n k hkn 1) =
    deriv (fun z : ℂ => L (F (a+Coeff.deletedSingleCLM n k hkn z))) 0
  exact hcomp.deriv.symm

/-- A locally selected sequence coordinate and its scalar contour
formula have the same retained-root directional derivative. -/
theorem deriv_sourcePsiSelectedEquationSequence_eq_deletedCoordinate
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hcoord : ∀ t ∈ U, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 (c m) (R m))
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (hpair : (a,ψ) ∈ U)
    (m k : ℤ) (hkn : k ≠ n) :
    deriv (fun z : ℂ =>
      (sourcePsiSelectedEquationSequence hp hp1 n c R
        (a+Coeff.deletedSingleCLM n k hkn z) ψ : Coeff p) m) 0 =
      deriv (fun z : ℂ =>
        sourcePsiDeletedEquationCoordinate hp hp1 n m
          (a+Coeff.deletedSingleCLM n k hkn z) ψ (c m) (R m)) 0 := by
  let line : ℂ → DeletedCoeff p n × CoeffPair p :=
    fun z => (a+Coeff.deletedSingleCLM n k hkn z,ψ)
  have hline0 : line 0 = (a,ψ) := by simp [line]
  have hlineCont : ContinuousAt line 0 := by
    dsimp [line]
    fun_prop
  have hUevent : ∀ᶠ z : ℂ in 𝓝 0, line z ∈ U := by
    exact hlineCont.eventually (show U ∈ 𝓝 (line 0) by
      rw [hline0]
      exact hUopen.mem_nhds hpair)
  have heq :
      (fun z : ℂ =>
        (sourcePsiSelectedEquationSequence hp hp1 n c R
          (a+Coeff.deletedSingleCLM n k hkn z) ψ : Coeff p) m) =ᶠ[𝓝 0]
      (fun z : ℂ =>
        sourcePsiDeletedEquationCoordinate hp hp1 n m
          (a+Coeff.deletedSingleCLM n k hkn z) ψ (c m) (R m)) := by
    filter_upwards [hUevent] with z hz
    change (sourcePsiSelectedEquationSequence hp hp1 n c R
      (a+Coeff.deletedSingleCLM n k hkn z) ψ : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          ((a+Coeff.deletedSingleCLM n k hkn z : DeletedCoeff p n) : Coeff p)
            ψ (c m) (R m)
    simpa only [line] using hcoord (line z) hz m
  exact heq.deriv_eq

/-- The actual bounded Jacobian matrix entry is the scalar contour
derivative computed in the psi variation lemmas. -/
theorem sourcePsiSelectedRootJacobian_entry_eq_deletedCoordinate
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hcoord : ∀ t ∈ U, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 (c m) (R m))
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (hpair : (a,ψ) ∈ U)
    (m k : ℤ) (hkn : k ≠ n) :
    ((sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
      (Coeff.deletedSingleCLM n k hkn 1) : DeletedCoeff p n) : Coeff p) m =
      deriv (fun z : ℂ =>
        sourcePsiDeletedEquationCoordinate hp hp1 n m
          (a+Coeff.deletedSingleCLM n k hkn z) ψ (c m) (R m)) 0 := by
  calc
    _ = deriv (fun z : ℂ =>
      (sourcePsiSelectedEquationSequence hp hp1 n c R
        (a+Coeff.deletedSingleCLM n k hkn z) ψ : Coeff p) m) 0 :=
        sourcePsiSelectedRootJacobian_entry_eq_deriv
          hp hp1 n c R U hUopen hdiff a ψ hpair m k hkn
    _ = _ := deriv_sourcePsiSelectedEquationSequence_eq_deletedCoordinate
      hp hp1 n c R U hUopen hcoord a ψ hpair m k hkn

/-- The locally holomorphic selected equation has one contour family
whose directional matrix entries agree with the scalar derivatives
used in the quantitative Lemma 12.5 estimates. -/
theorem exists_local_sourcePsi_selectedJacobian_entryFormula
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ K : ℕ, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        (∀ m : ℤ, K < m.natAbs →
          c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U → ∀ m k : ℤ, ∀ hkn : k ≠ n,
            deriv (fun z : ℂ =>
              (sourcePsiSelectedEquationSequence hp hp1 n c R
                (a+Coeff.deletedSingleCLM n k hkn z) ψ : Coeff p) m) 0 =
              deriv (fun z : ℂ =>
                sourcePsiDeletedEquationCoordinate hp hp1 n m
                  (a+Coeff.deletedSingleCLM n k hkn z) ψ (c m) (R m)) 0 := by
  obtain ⟨U,hUopen,hbase,K,c,R,_,hchoice,_,_,C,_,hcoord,_,_,_⟩ :=
    exists_local_sourcePsi_globalEquation_formula_analytic
      hp hp1 φ hφ n a₀
  refine ⟨U,hUopen,hbase,K,c,R,hchoice,?_⟩
  intro a ψ hpair m k hkn
  exact deriv_sourcePsiSelectedEquationSequence_eq_deletedCoordinate
    hp hp1 n c R U hUopen hcoord a ψ hpair m k hkn

/-- Near any real-type source, the Fréchet derivative of the selected
equation in its deleted root parameter is a bounded operator whose
matrix entries are exactly the scalar contour derivatives. -/
theorem exists_local_sourcePsi_selectedJacobian_matrixFormula
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
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
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U → ∀ m k : ℤ, ∀ hkn : k ≠ n,
            ((sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
              (Coeff.deletedSingleCLM n k hkn 1) : DeletedCoeff p n) : Coeff p) m =
              deriv (fun z : ℂ =>
                sourcePsiDeletedEquationCoordinate hp hp1 n m
                  (a+Coeff.deletedSingleCLM n k hkn z) ψ (c m) (R m)) 0 := by
  obtain ⟨U,hUopen,hbase,K,c,R,hcReal,hchoice,hgeom,hiso,C,_,hcoord,_,_,hdiff⟩ :=
    exists_local_sourcePsi_globalEquation_formula_analytic
      hp hp1 φ hφ n a₀
  refine ⟨U,hUopen,hbase,K,c,R,hcReal,hchoice,hgeom,hiso,?_⟩
  intro a ψ hpair m k hkn
  exact sourcePsiSelectedRootJacobian_entry_eq_deletedCoordinate
    hp hp1 n c R U hUopen hcoord hdiff a ψ hpair m k hkn

end NLS.ZakharovShabat
