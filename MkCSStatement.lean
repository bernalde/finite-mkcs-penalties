module

public import Chapter09NonlinearControls
public import Chapter09SharpnessControls
public import Chapter09SourceProcedure

/-! Independent proposition surfaces backed by unchanged accepted canonical proofs.
The original nonlinear ten-component proposition bundle is preserved exactly.
The extension adds linear/slack and actual sequential semantics with qualifications.
-/
@[expose] public section
noncomputable section
open scoped BigOperators

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
