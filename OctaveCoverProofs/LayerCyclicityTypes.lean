import Mathlib.Tactic

/-!
  ## LayerCyclicityTypes

  A 9-element cyclic type `Layer` (`L1`–`L9`) with a successor operation
  `transcend` and its inverse `descend`, together with enumeration and
  finiteness facts. The cyclicity property `transcend^9 = id` is proved in
  `GradedOctaveCover` (`transcend_nine`).
-/

namespace LayerCyclicityTypes

-- Types for a 9-element cyclic base.
--
-- The 9 layers (L1..L9) form a cyclic group of order 9 under the
-- "transcend" successor operation: applying transcend 9 times returns
-- to the starting layer. This is the cyclicity property transcend^9 = id,
-- proved in `GradedOctaveCover` (`transcend_nine`).

-- ============================================================
-- CORE LAYER TYPE
-- ============================================================

/-- A 9-element type with elements `L1` through `L9`.
    The "transcend" operation moves from one layer to the next,
    cycling back from L9 to L1. -/
inductive Layer where
  | L1 : Layer
  | L2 : Layer
  | L3 : Layer
  | L4 : Layer
  | L5 : Layer
  | L6 : Layer
  | L7 : Layer
  | L8 : Layer
  | L9 : Layer
  deriving BEq, DecidableEq

-- ============================================================
-- TRANSCEND OPERATION
-- ============================================================

/-- The transcend operation: successor function on layers.
    Maps each layer to the next, with L9 wrapping to L1.
    This is the generator of the cyclic group Z/9Z. -/
def transcend : Layer → Layer
  | .L1 => .L2
  | .L2 => .L3
  | .L3 => .L4
  | .L4 => .L5
  | .L5 => .L6
  | .L6 => .L7
  | .L7 => .L8
  | .L8 => .L9
  | .L9 => .L1

/-- Iterated transcend: apply transcend n times. -/
def transcend_n : Nat → Layer → Layer
  | 0, l => l
  | n + 1, l => transcend (transcend_n n l)

/-- The descend operation: predecessor function on layers.
    Inverse of transcend: maps each layer to the previous,
    with L1 wrapping to L9. -/
def descend : Layer → Layer
  | .L1 => .L9
  | .L2 => .L1
  | .L3 => .L2
  | .L4 => .L3
  | .L5 => .L4
  | .L6 => .L5
  | .L7 => .L6
  | .L8 => .L7
  | .L9 => .L8

-- ============================================================
-- LAYER ENUMERATION AND FINITENESS
-- ============================================================

/-- The complete list of all 9 layers. -/
def Layer.all : List Layer :=
  [.L1, .L2, .L3, .L4, .L5, .L6, .L7, .L8, .L9]

/-- Convert a layer to its numeric index (0-based). -/
def Layer.toNat : Layer → Nat
  | .L1 => 0
  | .L2 => 1
  | .L3 => 2
  | .L4 => 3
  | .L5 => 4
  | .L6 => 5
  | .L7 => 6
  | .L8 => 7
  | .L9 => 8

/-- Convert a Fin 9 to a Layer. -/
def Layer.ofFin : Fin 9 → Layer
  | ⟨0, _⟩ => .L1
  | ⟨1, _⟩ => .L2
  | ⟨2, _⟩ => .L3
  | ⟨3, _⟩ => .L4
  | ⟨4, _⟩ => .L5
  | ⟨5, _⟩ => .L6
  | ⟨6, _⟩ => .L7
  | ⟨7, _⟩ => .L8
  | ⟨8, _⟩ => .L9

/-- Every layer is in the enumeration. -/
theorem Layer.mem_all (l : Layer) : l ∈ Layer.all := by
  cases l <;> simp [Layer.all]

/-- The enumeration has exactly 9 elements. -/
theorem Layer.all_length : Layer.all.length = 9 := by
  rfl

/-- The enumeration has no duplicates. -/
theorem Layer.all_nodup : Layer.all.Nodup := by
  decide

/-- The orbit of a layer under transcend: list of all layers visited
    by iterating transcend starting from l. -/
def layerOrbit (l : Layer) : List Layer :=
  [l, transcend l, transcend_n 2 l, transcend_n 3 l,
   transcend_n 4 l, transcend_n 5 l, transcend_n 6 l,
   transcend_n 7 l, transcend_n 8 l]

end LayerCyclicityTypes
