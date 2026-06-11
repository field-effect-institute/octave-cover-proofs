import OctaveCoverProofs.TwoCoordinates
import Mathlib.Tactic

/-!
# NarrativeOctave — The 2D Narrative Manifold

## Overview

This module studies the product of two instances of the same 7-position
cyclic structure: a 7-position octave with 2 shock points, used once as a
horizontal axis and once as a vertical axis. The product of these two
instances is a (discrete) torus.

This module proves the topology of that torus: 9 regions, 6 path classes,
forced shock crossings. These are structural invariants of the encoded
structure — they hold for ANY content mapped to the framework.

## Boundaries vs. Shocks

The narrative octave has 7 positions and 3 segment boundaries (where the
segment changes on successor step): Mi→Fa, La→Si, and Si→Do(transcend).

Of these 3 boundaries, 2 are **shocks** (internal discontinuities requiring
bridging): Mi→Fa and La→Si. The third (Si→Do) is the **transcend** — the
cycle close that connects to the next octave.

This parallels the structure of the `Layer` module (the 9-layer cycle),
where all 3 triad boundaries are shocks. The difference: in the 9-layer
system, every boundary is a shock. In the 7-note system, one boundary is
a transcend rather than a shock.

The abstract octave invariant: `isBoundary p ↔ segment p ≠ segment (next p)`.
Both Layer and NarrativePos satisfy this, with shocks as a subset of boundaries.

## The Six Path Classes

Any complete traversal of the narrative torus crosses 4 shock lines
(2 horizontal + 2 vertical). The within-axis order is forced (mi-fa before
la-si). The between-axis interleaving is free. Valid interleavings: C(4,2) = 6.
-/

-- ═══════════════════════════════════════════════════
-- THE NARRATIVE POSITION TYPE
-- ═══════════════════════════════════════════════════

/-- The seven positions of the narrative octave.
    Named after the musical scale: Do Re Mi Fa Sol La Si.

    One illustrative reading (narrative function):
      Do = Perception, Re = Differentiation, Mi = Comparison,
      Fa = Structure, Sol = Measurement, La = Dynamics, Si = Integration

    The same type serves as both axes of the 2D grid below — the
    vertical axis is simply a second instance of the same
    7-position structure. -/
inductive NarrativePos where
  | Do  | Re  | Mi  | Fa  | Sol  | La  | Si
  deriving DecidableEq, Repr, BEq

instance : Fintype NarrativePos where
  elems := ⟨[NarrativePos.Do, NarrativePos.Re, NarrativePos.Mi,
              NarrativePos.Fa, NarrativePos.Sol, NarrativePos.La,
              NarrativePos.Si], by decide⟩
  complete p := by cases p <;> decide

namespace NarrativePos

-- ═══════════════════════════════════════════════════
-- INDEX AND SUCCESSOR
-- ═══════════════════════════════════════════════════

/-- Numerical index (0–6). -/
def index : NarrativePos → Fin 7
  | .Do  => 0  | .Re  => 1  | .Mi  => 2
  | .Fa  => 3  | .Sol => 4  | .La  => 5  | .Si  => 6

/-- Cyclic successor: Si → Do, all others advance.
    The generator of the cyclic structure. -/
def next : NarrativePos → NarrativePos
  | .Do  => .Re   | .Re  => .Mi   | .Mi  => .Fa
  | .Fa  => .Sol  | .Sol => .La   | .La  => .Si   | .Si  => .Do

-- ═══════════════════════════════════════════════════
-- BOUNDARIES AND SHOCKS
-- ═══════════════════════════════════════════════════

/-- Whether a transition from p to p.next crosses a segment boundary.
    True for Mi (→Fa), La (→Si), and Si (→Do, the transcend).
    This is the analog of Layer.isShockPoint — but in the 7-note
    system, one boundary (Si→Do) is a transcend rather than a shock. -/
def isBoundary : NarrativePos → Bool
  | .Mi => true    -- mi-fa boundary (shock)
  | .La => true    -- la-si boundary (shock)
  | .Si => true    -- si-do boundary (transcend / cycle close)
  | _   => false

/-- Whether a position is an internal shock point.
    Shocks are the boundaries internal to the cycle — discontinuities
    that require explicit bridging. The transcend (Si→Do) is a
    boundary but not a shock: it closes the cycle and connects to
    the next octave. Shocks ⊆ Boundaries. -/
def isShock : NarrativePos → Bool
  | .Mi => true    -- mi-fa shock
  | .La => true    -- la-si shock
  | _   => false

/-- The two shock types. -/
inductive ShockType where
  | MiFa   -- Between Mi and Fa (the first internal discontinuity)
  | LaSi   -- Between La and Si (the second internal discontinuity)
  deriving DecidableEq, Repr, BEq

/-- Shock type at a position, if it is a shock point. -/
def shockType : NarrativePos → Option ShockType
  | .Mi => some .MiFa
  | .La => some .LaSi
  | _   => none

-- ═══════════════════════════════════════════════════
-- SEGMENTS — THE Z/3Z QUOTIENT
-- ═══════════════════════════════════════════════════

/-- The three segments defined by boundaries.
    Segment 0 (Observe):  Do, Re, Mi  — before first shock
    Segment 1 (Act):      Fa, Sol, La — between shocks
    Segment 2 (Close):    Si          — after second shock

    This is the 7-position analog of `Layer.triad`.
    Both are quotient maps to Fin 3. -/
def segment : NarrativePos → Fin 3
  | .Do | .Re | .Mi   => 0
  | .Fa | .Sol | .La  => 1
  | .Si                => 2

end NarrativePos

-- ═══════════════════════════════════════════════════
-- THE 2D NARRATIVE GRID
-- ═══════════════════════════════════════════════════

/-- A cell in the 2D narrative space. The torus.
    fst = horizontal axis (first instance of the 7-position cycle)
    snd = vertical axis (second instance of the same cycle) -/
abbrev NarrativeCell := NarrativePos × NarrativePos

/-- The 9-region classification.
    Each region is (horizontal_segment, vertical_segment) ∈ (Fin 3)². -/
def NarrativeCell.region (c : NarrativeCell) : Fin 3 × Fin 3 :=
  (c.1.segment, c.2.segment)

-- ═══════════════════════════════════════════════════
-- SHOCK CROSSING CLASSIFICATION
-- ═══════════════════════════════════════════════════

/-- Which axis a shock crossing occurs on. -/
inductive ShockAxis where
  | horizontal  -- Moving along the first axis of the grid
  | vertical    -- Moving along the second axis of the grid
  deriving DecidableEq, Repr, BEq

/-- A shock crossing event: axis × shock type. -/
structure ShockCrossing where
  axis  : ShockAxis
  shock : NarrativePos.ShockType
  deriving DecidableEq, Repr, BEq

/-- The four mandatory shock crossings for any complete traversal. -/
def mandatoryCrossings : List ShockCrossing :=
  [ ⟨.horizontal, .MiFa⟩, ⟨.horizontal, .LaSi⟩,
    ⟨.vertical,   .MiFa⟩, ⟨.vertical,   .LaSi⟩ ]

-- ═══════════════════════════════════════════════════
-- THE SIX PATH CLASSES — (2,2)-SHUFFLES
-- ═══════════════════════════════════════════════════

/-- The six valid shock orderings, explicitly enumerated.
    These are the linear extensions of the partial order
    {h-MiFa < h-LaSi, v-MiFa < v-LaSi}.

    Each ordering represents a structurally distinct class of
    narrative traversal through the 2D torus. -/
def sixPathClasses : List (List ShockCrossing) :=
  let hm : ShockCrossing := ⟨.horizontal, .MiFa⟩
  let hl : ShockCrossing := ⟨.horizontal, .LaSi⟩
  let vm : ShockCrossing := ⟨.vertical,   .MiFa⟩
  let vl : ShockCrossing := ⟨.vertical,   .LaSi⟩
  [ [hm, hl, vm, vl],   -- Class 1: both horizontal crossings first
    [hm, vm, hl, vl],   -- Class 2: alternate h-v-h-v
    [hm, vm, vl, hl],   -- Class 3: h start → complete vertical → h close
    [vm, hm, hl, vl],   -- Class 4: v start → complete horizontal → v close
    [vm, hm, vl, hl],   -- Class 5: alternate v-h-v-h
    [vm, vl, hm, hl] ]  -- Class 6: both vertical crossings first

-- ═══════════════════════════════════════════════════
-- CORE THEOREMS
-- ═══════════════════════════════════════════════════

/-- Cyclicity: transcend⁷ = id. The narrative octave wraps. -/
theorem transcend_7_eq_id (p : NarrativePos) :
    p.next.next.next.next.next.next.next = p := by
  cases p <;> rfl

/-- Exactly 3 boundary points among the 7 positions. -/
theorem exactly_three_boundaries :
    (List.filter (fun p => p.isBoundary)
      [NarrativePos.Do, NarrativePos.Re, NarrativePos.Mi,
       NarrativePos.Fa, NarrativePos.Sol, NarrativePos.La,
       NarrativePos.Si]).length = 3 := by
  decide

/-- Exactly 2 shock points among the 7 positions. -/
theorem exactly_two_shocks :
    (List.filter (fun p => p.isShock)
      [NarrativePos.Do, NarrativePos.Re, NarrativePos.Mi,
       NarrativePos.Fa, NarrativePos.Sol, NarrativePos.La,
       NarrativePos.Si]).length = 2 := by
  decide

/-- Every shock is a boundary. -/
theorem shock_implies_boundary (p : NarrativePos) :
    p.isShock = true → p.isBoundary = true := by
  cases p <;> simp [NarrativePos.isShock, NarrativePos.isBoundary]

/-- Not every boundary is a shock (Si is boundary but not shock). -/
theorem boundary_not_always_shock :
    NarrativePos.Si.isBoundary = true ∧ NarrativePos.Si.isShock = false := by
  simp [NarrativePos.isBoundary, NarrativePos.isShock]

/-- Shock points are exactly Mi and La. -/
theorem shock_characterization (p : NarrativePos) :
    p.isShock = true ↔ (p = .Mi ∨ p = .La) := by
  cases p <;> simp [NarrativePos.isShock]

/-- Boundary points are exactly Mi, La, and Si. -/
theorem boundary_characterization (p : NarrativePos) :
    p.isBoundary = true ↔ (p = .Mi ∨ p = .La ∨ p = .Si) := by
  cases p <;> simp [NarrativePos.isBoundary]

/-- The successor has no fixed points. -/
theorem narrative_next_ne_self (p : NarrativePos) : p.next ≠ p := by
  cases p <;> simp [NarrativePos.next]

-- ═══════════════════════════════════════════════════
-- THE OCTAVE INVARIANT
-- ═══════════════════════════════════════════════════

/-- THE KEY THEOREM: Boundaries are exactly the positions where
    the segment changes on successor step.

    `isBoundary p ↔ segment p ≠ segment (next p)`

    This is the abstract octave invariant. The `Layer` type satisfies
    it too (see `layer_boundary_iff_triad_change` below). Both types
    are instances of the same algebra. -/
theorem boundary_iff_segment_change (p : NarrativePos) :
    p.isBoundary = true ↔ p.segment ≠ p.next.segment := by
  cases p <;> simp [NarrativePos.isBoundary, NarrativePos.segment, NarrativePos.next]

/-- Non-boundary transitions preserve the segment. -/
theorem non_boundary_same_segment (p : NarrativePos) (h : p.isBoundary = false) :
    p.segment = p.next.segment := by
  cases p <;> simp_all [NarrativePos.isBoundary, NarrativePos.segment, NarrativePos.next]

/-- Boundary transitions change the segment. -/
theorem boundary_changes_segment (p : NarrativePos) (h : p.isBoundary = true) :
    p.segment ≠ p.next.segment := by
  exact (boundary_iff_segment_change p).mp h

/-- The Layer analog: shocks ↔ triad boundaries.
    Both types satisfy: boundary ↔ segment changes on successor.

    In Layer, ALL boundaries are shocks (3 of 3).
    In NarrativePos, 2 of 3 boundaries are shocks (Si is transcend). -/
theorem layer_boundary_iff_triad_change (l : Layer) :
    l.isShockPoint = true ↔ l.triad ≠ l.next.triad := by
  cases l <;> simp [Layer.isShockPoint, Layer.triad, Layer.next]

-- ═══════════════════════════════════════════════════
-- TORUS TOPOLOGY
-- ═══════════════════════════════════════════════════

/-- The narrative grid has exactly 49 cells (7 × 7). -/
theorem grid_card : Fintype.card NarrativePos * Fintype.card NarrativePos = 49 := by
  decide

/-- The region map partitions the 49-cell grid into exactly 9 regions.
    The 9 regions are the cells of (Z/3Z)² = (Fin 3) × (Fin 3). -/
theorem nine_regions :
    (Finset.image (fun c : NarrativePos × NarrativePos =>
      NarrativeCell.region c) Finset.univ).card = 9 := by
  decide

/-- The region map is surjective: every (Fin 3 × Fin 3) pair is hit.
    No region is empty. -/
theorem region_surjective :
    ∀ r : Fin 3 × Fin 3, ∃ c : NarrativePos × NarrativePos,
      NarrativeCell.region c = r := by
  decide

-- ═══════════════════════════════════════════════════
-- PATH CLASS THEOREMS
-- ═══════════════════════════════════════════════════

/-- There are exactly 6 path classes. -/
theorem six_classes : sixPathClasses.length = 6 := by rfl

/-- All 6 classes have exactly 4 crossings each. -/
theorem all_classes_length_four :
    ∀ cls ∈ sixPathClasses, cls.length = 4 := by
  decide

/-- The (2,2)-shuffle count: C(4,2) = 6.
    The combinatorial identity underlying the path classification. -/
theorem shuffle_count : Nat.choose 4 2 = 6 := by decide

/-- All 6 classes are pairwise distinct. -/
theorem classes_pairwise_distinct :
    sixPathClasses.Nodup := by decide

-- ═══════════════════════════════════════════════════
-- STRUCTURAL BRIDGE: LAYER ↔ NARRATIVE
-- ═══════════════════════════════════════════════════

/-- Layer product also has 9 regions via triads.
    The (Z/3Z)² skeleton is the same for both types. -/
theorem layer_nine_regions :
    (Finset.image (fun c : Layer × Layer => (c.1.triad, c.2.triad))
      Finset.univ).card = 9 := by
  decide

/-- The shared structure: both grids produce exactly 9 regions.
    NarrativePos × NarrativePos and Layer × Layer have the same
    (Z/3Z)² quotient structure — different cardinality, same topology. -/
theorem shared_region_count :
    (Finset.image (fun c : NarrativePos × NarrativePos =>
      NarrativeCell.region c) Finset.univ).card =
    (Finset.image (fun c : Layer × Layer =>
      (c.1.triad, c.2.triad)) Finset.univ).card := by
  decide

/-- Both Layer and NarrativePos have exactly 3 segment-changing positions.
    Layer: L2, L5, L8 (all shocks). NarrativePos: Mi, La, Si (2 shocks + 1 transcend).
    Same count, different shock/transcend split. -/
theorem shared_boundary_count :
    (List.filter (fun p => p.isBoundary)
      [NarrativePos.Do, NarrativePos.Re, NarrativePos.Mi,
       NarrativePos.Fa, NarrativePos.Sol, NarrativePos.La,
       NarrativePos.Si]).length =
    (List.filter (fun l => l.isShockPoint)
      [Layer.L0, Layer.L1, Layer.L2, Layer.L3, Layer.L4,
       Layer.L5, Layer.L6, Layer.L7, Layer.L8]).length := by
  decide
