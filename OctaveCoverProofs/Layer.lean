
/-!
# Layer — A 9-Element Layered Cycle

A 9-layer model (L0-L8) forming the layered (vertical) axis of the
structure formalized in this development. Layers form a cycle
(transcend^9 = id), divide into 3 triads, and are punctuated by
3 shock points at octave boundaries.

The shock naming follows Bennett's three-octave model: the shocks at
L2→L3, L5→L6, and L8→L0 are labeled Mechanical, Intentional, and
Transcendent respectively.

These theorems certify properties of the encoded structure itself,
not any empirical claim about systems the layers may be used to model.
-/

-- ═══════════════════════════════════════════════════
-- THE 9 LAYERS
-- ═══════════════════════════════════════════════════

/-- The nine layers (L0-L8).
    These form the layered (vertical) axis of the structure. -/
inductive Layer where
  | L0  -- Substrate: raw undifferentiated material
  | L1  -- Observation: directed attention
  | L2  -- Pattern: vocabulary, coherent groupings
  | L3  -- Framework: structured models
  | L4  -- Strategy: planning cycles
  | L5  -- Collective Intelligence: multi-agent emergence
  | L6  -- Ethics: value alignment, constraints
  | L7  -- Emergence: genuinely new properties
  | L8  -- Transcendence: cyclic return
  deriving DecidableEq, Repr, BEq

/-- Human-readable layer name. -/
def Layer.name : Layer → String
  | .L0 => "Substrate"
  | .L1 => "Observation"
  | .L2 => "Pattern"
  | .L3 => "Framework"
  | .L4 => "Strategy"
  | .L5 => "Collective Intelligence"
  | .L6 => "Ethics"
  | .L7 => "Emergence"
  | .L8 => "Transcendence"

/-- Layer index (0-8). -/
def Layer.index : Layer → Nat
  | .L0 => 0
  | .L1 => 1
  | .L2 => 2
  | .L3 => 3
  | .L4 => 4
  | .L5 => 5
  | .L6 => 6
  | .L7 => 7
  | .L8 => 8

-- ═══════════════════════════════════════════════════
-- CYCLIC SUCCESSOR
-- ═══════════════════════════════════════════════════

/-- The cyclic successor: L8.next = L0, all others advance by one.
    This encodes the fundamental cyclicity of the layer model. -/
def Layer.next : Layer → Layer
  | .L0 => .L1
  | .L1 => .L2
  | .L2 => .L3
  | .L3 => .L4
  | .L4 => .L5
  | .L5 => .L6
  | .L6 => .L7
  | .L7 => .L8
  | .L8 => .L0

-- ═══════════════════════════════════════════════════
-- TRIADS
-- ═══════════════════════════════════════════════════

/-- The three triads that partition the 9 layers.
    Triad1: material (L0,L1,L2)
    Triad2: structural (L3,L4,L5)
    Triad3: integrative (L6,L7,L8) -/
inductive Triad where
  | first   -- Material: L0, L1, L2
  | second  -- Structural: L3, L4, L5
  | third   -- Integrative: L6, L7, L8
  deriving DecidableEq, Repr, BEq

/-- Which triad a layer belongs to. -/
def Layer.triad : Layer → Triad
  | .L0 | .L1 | .L2 => .first
  | .L3 | .L4 | .L5 => .second
  | .L6 | .L7 | .L8 => .third

-- ═══════════════════════════════════════════════════
-- SHOCK POINTS
-- ═══════════════════════════════════════════════════

/-- The three types of shock at octave boundaries.
    Named after Bennett's energy classification:
    - Mechanical: automatic, requires no consciousness (L2→L3)
    - Intentional: requires conscious effort (L5→L6)
    - Transcendent: cycle-closing, highest energy (L8→L0) -/
inductive ShockType where
  | Mechanical    -- L2→L3: Pattern → Framework
  | Intentional   -- L5→L6: Collective Intelligence → Ethics
  | Transcendent  -- L8→L0: Transcendence → Substrate (cycle close)
  deriving DecidableEq, Repr, BEq

/-- Whether a layer transition to its successor is a shock point.
    Shock points occur at triad boundaries: L2→L3, L5→L6, L8→L0. -/
def Layer.isShockPoint : Layer → Bool
  | .L2 => true   -- Mechanical shock
  | .L5 => true   -- Intentional shock
  | .L8 => true   -- Transcendent shock
  | _   => false

/-- The shock type at a layer transition, if it is a shock point. -/
def Layer.shockType : Layer → Option ShockType
  | .L2 => some .Mechanical
  | .L5 => some .Intentional
  | .L8 => some .Transcendent
  | _   => none

-- ═══════════════════════════════════════════════════
-- ITERATED SUCCESSOR
-- ═══════════════════════════════════════════════════

/-- Apply the cyclic successor n times. -/
def Layer.iterate (l : Layer) (n : Nat) : Layer :=
  match n with
  | 0     => l
  | n + 1 => (l.next).iterate n

-- ═══════════════════════════════════════════════════
-- CORE THEOREMS
-- ═══════════════════════════════════════════════════

/-- The fundamental cyclicity theorem: applying next 9 times
    returns to the same layer. transcend^9 = id. -/
theorem transcend_9_eq_id (l : Layer) : l.iterate 9 = l := by
  cases l <;> rfl

/-- Every layer's shock status is decidable. -/
theorem shock_decidable (l : Layer) :
    l.isShockPoint = true ∨ l.isShockPoint = false := by
  cases l <;> simp [Layer.isShockPoint]

/-- There are exactly 3 shock points among the 9 layers. -/
theorem exactly_three_shocks :
    (List.filter (fun l => l.isShockPoint)
      [Layer.L0, Layer.L1, Layer.L2, Layer.L3, Layer.L4,
       Layer.L5, Layer.L6, Layer.L7, Layer.L8]).length = 3 := by
  decide

/-- Shock points coincide exactly with triad boundaries:
    a layer is a shock point iff it is the last element of its triad. -/
theorem shock_iff_triad_boundary (l : Layer) :
    l.isShockPoint = true ↔
      (l = .L2 ∨ l = .L5 ∨ l = .L8) := by
  cases l <;> simp [Layer.isShockPoint]

/-- A shock point always has an associated ShockType. -/
theorem shock_has_type (l : Layer) (h : l.isShockPoint = true) :
    l.shockType.isSome = true := by
  cases l <;> simp [Layer.isShockPoint, Layer.shockType] at *

/-- A non-shock layer has no shock type. -/
theorem no_shock_no_type (l : Layer) (h : l.isShockPoint = false) :
    l.shockType = none := by
  cases l <;> simp [Layer.isShockPoint, Layer.shockType] at *

/-- The cyclic successor always changes the layer (no fixed points). -/
theorem next_ne_self (l : Layer) : l.next ≠ l := by
  cases l <;> simp [Layer.next]

/-- iterate 0 is identity. -/
theorem iterate_zero (l : Layer) : l.iterate 0 = l := by
  rfl

/-- iterate composes: iterate (m + n) = iterate n ∘ iterate m. -/
theorem iterate_add (l : Layer) (m n : Nat) :
    l.iterate (m + n) = (l.iterate m).iterate n := by
  induction m generalizing l with
  | zero => simp [Layer.iterate]
  | succ k ih =>
    simp [Layer.iterate]
    rw [Nat.succ_add]
    simp [Layer.iterate]
    exact ih l.next

/-- Every layer belongs to exactly one triad (well-definedness witness). -/
theorem triad_covers_all (l : Layer) :
    l.triad = .first ∨ l.triad = .second ∨ l.triad = .third := by
  cases l <;> simp [Layer.triad]

/-- Crossing a shock point changes the triad. -/
theorem shock_changes_triad (l : Layer) (h : l.isShockPoint = true) :
    l.triad ≠ l.next.triad := by
  cases l <;> simp [Layer.isShockPoint, Layer.triad, Layer.next] at *

/-- Non-shock transitions stay within the same triad. -/
theorem non_shock_same_triad (l : Layer) (h : l.isShockPoint = false) :
    l.triad = l.next.triad := by
  cases l <;> simp [Layer.isShockPoint, Layer.triad, Layer.next] at *
