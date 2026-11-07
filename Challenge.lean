module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Finite nonlinear MkCS exact penalties.
Definitions below preserve the accepted finite model; Statement packages the
proved components. Only Challenge.lean contains the deliberate proof placeholder.
The color product sums over ordered distinct pairs: its coefficient is c2,
so an unordered-pair formulation has coefficient 2*c2.
-/
@[expose] public section
noncomputable section
open scoped BigOperators
namespace Chapter09
variable {α : Type*} [DecidableEq α]

def conflicts (E : Finset (α × α)) (S : Finset α) : Finset (α × α) :=
  E.filter (fun e => e.1 ∈ S ∧ e.2 ∈ S)

def feasible (E : Finset (α × α)) (S : Finset α) : Prop :=
  ∀ e ∈ E, ¬ (e.1 ∈ S ∧ e.2 ∈ S)

def score (E : Finset (α × α)) (w : α × α → ℝ) (S : Finset α) : ℝ :=
  (S.card : ℝ) - ∑ e ∈ conflicts E S, w e

def cover (E : Finset (α × α)) (S : Finset α) : Finset α :=
  (conflicts E S).image Prod.fst

def repair (E : Finset (α × α)) (S : Finset α) : Finset α :=
  S \ cover E S

end Chapter09

namespace Chapter09.Source

abbrev Slot (n k : ℕ) := Fin n × Fin k

structure Graph (n : ℕ) where
  edges : Finset (Fin n × Fin n)
  ordered : ∀ e ∈ edges, e.1 < e.2

def flag {n k : ℕ} (S : Finset (Slot n k)) (i : Fin n) (r : Fin k) : ℝ :=
  if (i, r) ∈ S then 1 else 0

def row {n k : ℕ} (S : Finset (Slot n k)) (i : Fin n) : Finset (Fin k) :=
  Finset.univ.filter (fun r => (i, r) ∈ S)

def rowCount {n k : ℕ} (S : Finset (Slot n k)) (i : Fin n) : ℕ := (row S i).card

def vertices {n k : ℕ} (S : Finset (Slot n k)) : Finset (Fin n) := S.image Prod.fst

def spatialPairs {n : ℕ} (G : Graph n) (k : ℕ) : Finset (Slot n k × Slot n k) :=
  Finset.univ.filter (fun e => (e.1.1, e.2.1) ∈ G.edges ∧ e.1.2 = e.2.2)

def colorPairs (n k : ℕ) : Finset (Slot n k × Slot n k) :=
  Finset.univ.filter (fun e => e.1.1 = e.2.1 ∧ e.1.2 < e.2.2)

def conflictPairs {n : ℕ} (G : Graph n) (k : ℕ) := spatialPairs G k ∪ colorPairs n k

def Feasible {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) : Prop :=
  Chapter09.feasible (conflictPairs G k) S

@[simp] theorem feasible_empty {n : ℕ} (G : Graph n) (k : ℕ) :
    Feasible G (∅ : Finset (Slot n k)) := by
  intro e _ h
  exact Finset.notMem_empty e.1 h.1

def maxPoint {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) : ι :=
  Classical.choose (s.exists_max_image f hs)

def maxOn {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) : ℝ :=
  f (maxPoint s hs f)

def finiteMax {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) : ℝ :=
  maxOn Finset.univ Finset.univ_nonempty f

def feasibleSelections {n : ℕ} (G : Graph n) (k : ℕ) : Finset (Finset (Slot n k)) := by
  classical
  exact Finset.univ.filter (Feasible G)

@[simp] theorem mem_feasibleSelections {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) :
    S ∈ feasibleSelections G k ↔ Feasible G S := by classical simp [feasibleSelections]

theorem feasibleSelections_nonempty {n : ℕ} (G : Graph n) (k : ℕ) :
    (feasibleSelections G k).Nonempty := ⟨∅, by simp⟩

def alpha {n : ℕ} (G : Graph n) (k : ℕ) : ℝ :=
  maxOn (feasibleSelections G k) (feasibleSelections_nonempty G k) (fun S => ((vertices S).card : ℝ))

def Binary {n k : ℕ} (x : Fin n → Fin k → ℝ) : Prop := ∀ i r, x i r = 0 ∨ x i r = 1

def reward {n k : ℕ} (S : Finset (Slot n k)) : ℝ := ∑ i, ∑ r, flag S i r ^ 2

def edgeProducts {n k : ℕ} (G : Graph n) (S : Finset (Slot n k)) : ℝ :=
  ∑ e ∈ G.edges, ∑ r, flag S e.1 r * flag S e.2 r

def orderedProducts {n k : ℕ} (S : Finset (Slot n k)) : ℝ :=
  ∑ i, ∑ r, ∑ p, if p ≠ r then flag S i r * flag S i p else 0

def colorProducts {n k : ℕ} (S : Finset (Slot n k)) : ℝ :=
  ∑ i, ∑ r, ∑ p, if r < p then flag S i r * flag S i p else 0

def nScore {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (S : Finset (Slot n k)) : ℝ :=
  reward S - c1 * edgeProducts G S - c2 * orderedProducts S

def arrayNScore {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (x : Fin n → Fin k → ℝ) : ℝ :=
  (∑ i, ∑ r, x i r ^ 2) - c1 * (∑ e ∈ G.edges, ∑ r, x e.1 r * x e.2 r) -
    c2 * (∑ i, ∑ r, ∑ p, if p ≠ r then x i r * x i p else 0)

def qNonlinear {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ) : ℝ :=
  finiteMax (nScore (k := k) G c1 c2)

def isNMax {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (S : Finset (Slot n k)) : Prop :=
  ∀ T : Finset (Slot n k), nScore G c1 c2 T ≤ nScore G c1 c2 S

end Chapter09.Source

namespace Chapter09.Source.Controls

def emptyGraph (n : ℕ) : Graph n := ⟨∅,by simp⟩

def twoVertexEdge : Graph 2 :=
  ⟨{(0,1)},by
    intro e he
    have h : e = (0,1) := by simpa using he
    subst e
    decide⟩

end Chapter09.Source.Controls


namespace Chapter09.Source

/-- One stored undirected edge and one color; edge membership remains part of the index. -/
abbrev EdgeIndex {n : ℕ} (G : Graph n) (k : ℕ) :=
  {e : Fin n × Fin n // e ∈ G.edges} × Fin k

/-- Joint binary x,s,t domain: selected slots, Boolean edge slacks and Boolean vertex slacks. -/
abbrev LState {n : ℕ} (G : Graph n) (k : ℕ) :=
  Finset (Slot n k) × (EdgeIndex G k → Bool) × (Fin n → Bool)

/-- Interpret a Boolean slack as the real number zero or one. -/
def boolValue (b : Bool) : ℝ := if b = true then 1 else 0

/-- Literal linear edge-row residual for one edge/color index. -/
def edgeResidual {n k : ℕ} (G : Graph n) (S : Finset (Slot n k))
    (s : EdgeIndex G k → Bool) (er : EdgeIndex G k) : ℝ :=
  flag S er.1.val.1 er.2 + flag S er.1.val.2 er.2 + boolValue (s er) - 1

/-- Sum of squared edge-row residuals over all stored edge/color indices. -/
def edgePenalty {n k : ℕ} (G : Graph n) (S : Finset (Slot n k))
    (s : EdgeIndex G k → Bool) : ℝ := ∑ er, edgeResidual G S s er ^ 2

/-- Sum of squared vertex/color-count residuals with binary vertex slacks. -/
def vertexPenalty {n k : ℕ} (S : Finset (Slot n k)) (t : Fin n → Bool) : ℝ :=
  ∑ i, ((∑ r, flag S i r) + boolValue (t i) - 1) ^ 2

/-- Literal linear QUBO reward minus the two squared-residual penalties. -/
def lScore {n : ℕ} {k : ℕ} (G : Graph n) (c1 c2 : ℝ) (z : LState G k) : ℝ :=
  (∑ i, ∑ r, flag z.1 i r ^ 2) - c1 * edgePenalty G z.1 z.2.1 -
    c2 * vertexPenalty z.1 z.2.2

/-- Actual attained finite maximum over the full joint binary slack domain. -/
def qLinear {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ) : ℝ :=
  finiteMax (lScore (k := k) G c1 c2)

/-- Global maximizer on all joint binary states, without fixing any slack assignment. -/
def IsLMax {n k : ℕ} (G : Graph n) (c1 c2 : ℝ) (z : LState G k) : Prop :=
  ∀ w : LState G k, lScore G c1 c2 w ≤ lScore G c1 c2 z

/-- Every real array entry is exactly zero or one. -/
def BinaryValues {α : Type*} (f : α → ℝ) : Prop := ∀ a, f a = 0 ∨ f a = 1

/-- The same literal linear objective on separately quantified real x,s,t arrays. -/
def arrayLScore {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (x : Fin n → Fin k → ℝ) (s : EdgeIndex G k → ℝ) (t : Fin n → ℝ) : ℝ :=
  (∑ i, ∑ r, x i r ^ 2) -
    c1 * (∑ er : EdgeIndex G k, (x er.1.val.1 er.2 + x er.1.val.2 er.2 + s er - 1)^2) -
    c2 * (∑ i, ((∑ r, x i r) + t i - 1)^2)

end Chapter09.Source

namespace Chapter09.ConflictDeletion
variable {α : Type*} [DecidableEq α]

def edgeStep (S : Finset α) (e : α × α) : Finset α :=
  if e.1 ∈ S ∧ e.2 ∈ S then S.erase e.1 else S

def edgeScan : List (α × α) → Finset α → Finset α
  | [], S => S
  | e :: es, S => edgeScan es (edgeStep S e)

end Chapter09.ConflictDeletion

namespace Chapter09.Sequential
open Source ConflictDeletion
variable {n k : ℕ}

def rowStep (S : Finset (Slot n k)) (u : Slot n k) : Finset (Slot n k) :=
  if u ∈ S ∧ ∃ p : Fin k, p ≠ u.2 ∧ (u.1,p) ∈ S then S.erase u else S

def rowScan : List (Slot n k) → Finset (Slot n k) → Finset (Slot n k)
  | [], S => S
  | u :: us, S => rowScan us (rowStep S u)

def algorithm (LE : List (Slot n k × Slot n k)) (LV : List (Slot n k))
    (S : Finset (Slot n k)) : Finset (Slot n k) := rowScan LV (edgeScan LE S)

end Chapter09.Sequential

namespace PalomarMkCS
open Chapter09.Source


/-- Exact maximum over all binary arrays, with no positivity requirement. -/
def BinaryMaximum : Prop :=
  ∀ {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ),
    (∃ x : Fin n → Fin k → ℝ,
      Binary x ∧ arrayNScore G c1 c2 x = qNonlinear G k c1 c2) ∧
    ∀ x : Fin n → Fin k → ℝ,
      Binary x → arrayNScore G c1 c2 x ≤ qNonlinear G k c1 c2

/-- The normalization is part of the statement, not an implicit convention. -/
def OrderedNormalization : Prop :=
  ∀ {n k : ℕ} (S : Finset (Slot n k)), orderedProducts S = 2 * colorProducts S

/-- Weak penalties preserve the value, not feasibility of every optimizer. -/
def WeakValue : Prop :=
  ∀ {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ),
    1 ≤ c1 → 1 ≤ 2*c2 → qNonlinear G k c1 c2 = alpha G k

/-- Auxiliary simultaneous deletion; this does not assert Algorithm12 semantics. -/
def WeakRepair : Prop :=
  ∀ {n k : ℕ} (G : Graph n) (c1 c2 : ℝ),
    1 ≤ c1 → 1 ≤ 2*c2 → ∀ S : Finset (Slot n k), isNMax G c1 c2 S →
      Feasible G (Chapter09.repair (conflictPairs G k) S) ∧
      ((Chapter09.repair (conflictPairs G k) S).card : ℝ) = alpha G k

/-- Strict effective penalties make every global optimizer feasible. -/
def StrictOptimizer : Prop :=
  ∀ {n k : ℕ} (G : Graph n) (c1 c2 : ℝ),
    1 < c1 → 1 < 2*c2 → ∀ S : Finset (Slot n k), isNMax G c1 c2 S →
      Feasible G S ∧ (S.card : ℝ) = alpha G k

/-- With one color the ordered color term vanishes; c2 is any real. -/
def OneColorValue : Prop :=
  ∀ {n : ℕ} (G : Graph n) (c1 c2 : ℝ),
    1 ≤ c1 → qNonlinear G 1 c1 c2 = alpha G 1

def OneColorStrict : Prop :=
  ∀ {n : ℕ} (G : Graph n) (c1 c2 : ℝ), 1 < c1 →
    ∀ S : Finset (Slot n 1), isNMax G c1 c2 S →
      Feasible G S ∧ (S.card : ℝ) = alpha G 1

def OneColorRepair : Prop :=
  ∀ {n : ℕ} (G : Graph n) (c1 c2 : ℝ), 1 ≤ c1 →
    ∀ S : Finset (Slot n 1), isNMax G c1 c2 S →
      Feasible G (Chapter09.repair (conflictPairs G 1) S) ∧
      ((Chapter09.repair (conflictPairs G 1) S).card : ℝ) = alpha G 1

/-- An infeasible global maximum at the unit edge boundary. -/
def UnitEdgeTie : Prop :=
  ∀ c2 : ℝ,
    isNMax Controls.twoVertexEdge 1 c2 (Finset.univ : Finset (Slot 2 1)) ∧
    ¬ Feasible Controls.twoVertexEdge (Finset.univ : Finset (Slot 2 1))

/-- An infeasible global maximum at the ordered color boundary. -/
def HalfColorTie : Prop :=
  isNMax (Controls.emptyGraph 1) 1 (1/2) (Finset.univ : Finset (Slot 1 2)) ∧
  ¬ Feasible (Controls.emptyGraph 1) (Finset.univ : Finset (Slot 1 2))

/-- One coherent entry, rather than ten claimed research contributions. -/
def Statement : Prop :=
  BinaryMaximum ∧ OrderedNormalization ∧ WeakValue ∧ WeakRepair ∧
  StrictOptimizer ∧ OneColorValue ∧ OneColorStrict ∧ OneColorRepair ∧
  UnitEdgeTie ∧ HalfColorTie

end PalomarMkCS

namespace PalomarMkCS
open Chapter09.Source

/-- The full binary real-array domain attains exactly the finite Boolean-state optimum. -/
def LinearBinaryMaximum : Prop :=
  ∀ {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ),
    ∃ (x : Fin n → Fin k → ℝ) (s : EdgeIndex G k → ℝ) (t : Fin n → ℝ),
      Binary x ∧ BinaryValues s ∧ BinaryValues t ∧
      arrayLScore G c1 c2 x s t = qLinear G k c1 c2 ∧
      ∀ (y : Fin n → Fin k → ℝ) (u : EdgeIndex G k → ℝ) (v : Fin n → ℝ),
        Binary y → BinaryValues u → BinaryValues v →
        arrayLScore G c1 c2 y u v ≤ qLinear G k c1 c2

/-- Source strict linear theorem, including positive color count and arbitrary joint binary slacks. -/
def LinearStrict : Prop :=
  ∀ {n k : ℕ} (G : Graph n) (_hk : 0 < k) (c1 c2 : ℝ)
    (hc1 : 1 < c1) (hc2 : 1 < c2),
    qLinear G k c1 c2 = alpha G k ∧
    ∀ z : LState G k, IsLMax G c1 c2 z →
      Feasible G z.1 ∧ (z.1.card : ℝ) = alpha G k

/-- Weak unit linear penalties give value equality; every optimizer is not asserted feasible. -/
def LinearWeakValue : Prop :=
  ∀ {n : ℕ} (G : Graph n) (k : ℕ) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 1 ≤ c2),
    qLinear G k c1 c2 = alpha G k

/-- At one color the linear row-slack coefficient is still required nonnegative. -/
def LinearOneColorValue : Prop :=
  ∀ {n : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 0 ≤ c2),
    qLinear G 1 c1 c2 = alpha G 1

/-- Strict edge penalty and nonnegative row-slack penalty give one-color optimizer feasibility. -/
def LinearOneColorStrict : Prop :=
  ∀ {n : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 1 < c1) (hc2 : 0 ≤ c2) (z : LState G 1) (hz : IsLMax G c1 c2 z),
    Feasible G z.1 ∧ (z.1.card : ℝ) = alpha G 1

/-- Original unit-boundary nonlinear corollary with the actual exhaustive current-state Algorithm12. -/
def NonlinearSourceAlgorithm : Prop :=
  ∀ {n k : ℕ} (G : Graph n) (hk : 0 < k) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 1 ≤ c2) (hunit : c1 = 1 ∨ c2 = 1)
    (LE : List (Slot n k × Slot n k)) (LV : List (Slot n k))
    (hs : ∀ e ∈ LE, e ∈ spatialPairs G k) (hE : ∀ e ∈ spatialPairs G k, e ∈ LE)
    (hV : ∀ u : Slot n k, u ∈ LV) (S : Finset (Slot n k))
    (hm : isNMax G c1 c2 S),
    qNonlinear G k c1 c2 = alpha G k ∧
    Feasible G (Chapter09.Sequential.algorithm LE LV S) ∧
    ((Chapter09.Sequential.algorithm LE LV S).card : ℝ) = alpha G k

/-- Original unit-boundary linear corollary with actual current-state Algorithm12. -/
def LinearSourceAlgorithm : Prop :=
  ∀ {n k : ℕ} (G : Graph n) (_hk : 0 < k) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 1 ≤ c2) (_hunit : c1 = 1 ∨ c2 = 1)
    (LE : List (Slot n k × Slot n k)) (LV : List (Slot n k))
    (hs : ∀ e ∈ LE, e ∈ spatialPairs G k) (hE : ∀ e ∈ spatialPairs G k, e ∈ LE)
    (hV : ∀ u : Slot n k, u ∈ LV) (z : LState G k) (hz : IsLMax G c1 c2 z),
    qLinear G k c1 c2 = alpha G k ∧
    Feasible G (Chapter09.Sequential.algorithm LE LV z.1) ∧
    ((Chapter09.Sequential.algorithm LE LV z.1).card : ℝ) = alpha G k

/-- Actual sequential nonlinear repair at the corrected weak ordered threshold 2*c2>=1. -/
def NonlinearWeakAlgorithm : Prop :=
  ∀ {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 1 ≤ 2*c2)
    (LE : List (Slot n k × Slot n k)) (LV : List (Slot n k))
    (hs : ∀ e ∈ LE, e ∈ spatialPairs G k) (hE : ∀ e ∈ spatialPairs G k, e ∈ LE)
    (hV : ∀ u : Slot n k, u ∈ LV) (S : Finset (Slot n k))
    (hm : isNMax G c1 c2 S),
    Feasible G (Chapter09.Sequential.algorithm LE LV S) ∧
    nScore G c1 c2 S = ((Chapter09.Sequential.algorithm LE LV S).card : ℝ) ∧
    ((Chapter09.Sequential.algorithm LE LV S).card : ℝ) = alpha G k ∧
    ∀ T : Finset (Slot n k), Feasible G T →
      (T.card : ℝ) ≤ ((Chapter09.Sequential.algorithm LE LV S).card : ℝ)

/-- The one-color nonlinear sequential repair imposes no hypothesis on the color coefficient. -/
def NonlinearOneColorAlgorithm : Prop :=
  ∀ {n : ℕ} (G : Graph n) (c1 c2 : ℝ) (hc1 : 1 ≤ c1)
    (LE : List (Slot n 1 × Slot n 1)) (LV : List (Slot n 1))
    (hs : ∀ e ∈ LE, e ∈ spatialPairs G 1) (hE : ∀ e ∈ spatialPairs G 1, e ∈ LE)
    (hV : ∀ u : Slot n 1, u ∈ LV) (S : Finset (Slot n 1))
    (hm : isNMax G c1 c2 S),
    Feasible G (Chapter09.Sequential.algorithm LE LV S) ∧
    nScore G c1 c2 S = ((Chapter09.Sequential.algorithm LE LV S).card : ℝ) ∧
    ((Chapter09.Sequential.algorithm LE LV S).card : ℝ) = alpha G 1

/-- Actual sequential linear repair at both weak unit thresholds, for every joint maximizer. -/
def LinearWeakAlgorithm : Prop :=
  ∀ {n k : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 1 ≤ c2)
    (LE : List (Slot n k × Slot n k)) (LV : List (Slot n k))
    (hs : ∀ e ∈ LE, e ∈ spatialPairs G k) (hE : ∀ e ∈ spatialPairs G k, e ∈ LE)
    (hV : ∀ u : Slot n k, u ∈ LV) (z : LState G k) (hz : IsLMax G c1 c2 z),
    Feasible G (Chapter09.Sequential.algorithm LE LV z.1) ∧
    lScore G c1 c2 z = ((Chapter09.Sequential.algorithm LE LV z.1).card : ℝ) ∧
    ((Chapter09.Sequential.algorithm LE LV z.1).card : ℝ) = alpha G k

/-- One-color linear sequential repair retains nonnegative row-slack coefficient. -/
def LinearOneColorAlgorithm : Prop :=
  ∀ {n : ℕ} (G : Graph n) (c1 c2 : ℝ)
    (hc1 : 1 ≤ c1) (hc2 : 0 ≤ c2)
    (LE : List (Slot n 1 × Slot n 1)) (LV : List (Slot n 1))
    (hs : ∀ e ∈ LE, e ∈ spatialPairs G 1) (hE : ∀ e ∈ spatialPairs G 1, e ∈ LE)
    (hV : ∀ u : Slot n 1, u ∈ LV) (z : LState G 1) (hz : IsLMax G c1 c2 z),
    Feasible G (Chapter09.Sequential.algorithm LE LV z.1) ∧
    lScore G c1 c2 z = ((Chapter09.Sequential.algorithm LE LV z.1).card : ℝ) ∧
    ((Chapter09.Sequential.algorithm LE LV z.1).card : ℝ) = alpha G 1

/-- For fixed positive k and positive coefficients, characterize value equality over every n and graph. -/
def NonlinearUniversalValue : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (c1 c2 : ℝ)
    (_hc1 : 0 < c1) (_hc2 : 0 < c2),
    (∀ (n : ℕ) (G : Graph n), qNonlinear G k c1 c2 = alpha G k) ↔
      1 ≤ c1 ∧ (k = 1 ∨ 1/2 ≤ c2)

/-- Universal linear value equality has the one-color exception and unit multi-color threshold. -/
def LinearUniversalValue : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (c1 c2 : ℝ)
    (_hc1 : 0 < c1) (hc2 : 0 < c2),
    (∀ (n : ℕ) (G : Graph n), qLinear G k c1 c2 = alpha G k) ↔
      1 ≤ c1 ∧ (k = 1 ∨ 1 ≤ c2)

/-- Same strict nonlinear source theorem through the accepted manuscript-route proof; no new theorem credit. -/
def SourceRouteStrict : Prop :=
  ∀ {n k : ℕ} (G : Graph n) (_hk : 0 < k)
    (c1 c2 : ℝ) (hc1 : 1 < c1) (hc2 : 1 < c2),
    qNonlinear G k c1 c2 = alpha G k ∧
      ∀ S : Finset (Slot n k), isNMax G c1 c2 S →
        Feasible G S ∧ (S.card : ℝ) = alpha G k

/-- One coherent extension bundle; components are not independent research credits. -/
def ExtensionStatement : Prop :=
  LinearBinaryMaximum ∧
  LinearStrict ∧
  LinearWeakValue ∧
  LinearOneColorValue ∧
  LinearOneColorStrict ∧
  NonlinearSourceAlgorithm ∧
  LinearSourceAlgorithm ∧
  NonlinearWeakAlgorithm ∧
  NonlinearOneColorAlgorithm ∧
  LinearWeakAlgorithm ∧
  LinearOneColorAlgorithm ∧
  NonlinearUniversalValue ∧
  LinearUniversalValue ∧
  SourceRouteStrict

end PalomarMkCS

namespace PalomarMkCS

theorem solution : Statement := by sorry

theorem extension_solution : ExtensionStatement := by sorry

end PalomarMkCS
