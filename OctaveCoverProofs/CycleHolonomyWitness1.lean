import Mathlib.Tactic
import OctaveCoverProofs.LayerCyclicityTypes

/-!
  ## CycleHolonomyWitness1 — Discrete holonomy over the L1→…→L9→L1 base cycle

  **The object.** This is a *discrete* holonomy — an integer-valued connection on the 9-cycle
  base, summed once around the loop — NOT the continuous rotation number of a circle map.
  (The continuous analog — irrational rotations of S¹ and the classical Kronecker–Weyl
  equidistribution dichotomy — is standard mathematics; bridging to it would require first
  imposing a continuous-circle model, which this file deliberately does not do.)

  **Construction.**
  - Base: `Layer` (ℤ/9ℤ) under `transcend` (= +1 mod 9). The base loop is
    `layerOrbit .L1 = L1→…→L9`, which visits each of the nine layers exactly once
    (it reduces by computation to the full enumeration).
  - Fiber: the additive group `ℤ` (a displacement counter for the grade).
  - Connection: `Conn := Layer → ℤ` — the fiber displacement on each outgoing `transcend` edge.
  - Holonomy: total fiber displacement after one full base loop from L1.
    Flat ⟺ `holonomy δ = 0` (the loop closes in the fiber); winding ⟺ `≠ 0` (same base
    layer, nonzero net residual in the fiber).

  **Results (T1–T5).**
  - T1: the constant-1 connection has holonomy `9` — the observable can be nonzero.
  - T2: every coboundary `l ↦ g (transcend l) - g l` has holonomy `0` (telescoping).
  - T3: non-vacuity — the observable attains both zero and nonzero values, so a computed
    holonomy carries information.
  - T4: every coboundary connection is flat (T2 packaged via the `IsCoboundary` predicate).
  - T5: the coboundary of the layer-index potential is flat (T5a), while the constant-1
    "winding" connection is provably NOT a coboundary (T5b). Consequence: nonzero holonomy
    requires a connection outside the coboundary subgroup — an explicitly added assumption,
    never derivable from the base cyclic structure alone.

  These results certify the encoded structure only; no empirical claim is made.
-/

namespace CycleHolonomyWitness1

open LayerCyclicityTypes

/-- A connection assigns a fiber displacement (in ℤ) to each outgoing `transcend` edge,
    indexed by its source layer. -/
abbrev Conn : Type := Layer → ℤ

/-- Discrete holonomy: the total fiber displacement accumulated traversing the base
    9-cycle once, starting from `L1`. The base loop is `layerOrbit .L1`, which visits
    each of the nine layers exactly once. -/
def holonomy (δ : Conn) : ℤ := ((layerOrbit Layer.L1).map δ).sum

-- ============================================================
-- T1 — A winding instance exists (holonomy ≠ 0)
-- ============================================================

/-- **T1**. The unit connection (displacement `1` on every edge) has holonomy `9`:
    nine edges, each contributing `1`. Witnesses that the observable can be nonzero. -/
theorem holonomy_const_one_eq_nine : holonomy (fun _ => (1 : ℤ)) = 9 := by
  simp only [holonomy, layerOrbit, transcend_n, transcend,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

-- ============================================================
-- T2 — A flat instance exists for every potential (coboundary ⇒ flat)
-- ============================================================

/-- **T2** (telescoping / coboundary flatness). For any layer-potential `g : Layer → ℤ`,
    the coboundary connection `l ↦ g (transcend l) - g l` has holonomy `0`.

    Because the base loop `layerOrbit .L1` visits each layer exactly once and `transcend`
    permutes the layers, the sum telescopes:
    `Σ (g (transcend l) - g l) = 0`. Concretely, summing over `L1,…,L9` the terms
    `(g L2 − g L1) + (g L3 − g L2) + … + (g L1 − g L9)` cancel pairwise. -/
theorem holonomy_coboundary (g : Layer → ℤ) :
    holonomy (fun l => g (transcend l) - g l) = 0 := by
  simp only [holonomy, layerOrbit, transcend_n, transcend,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

-- ============================================================
-- T3 — non-vacuity: the observable takes both 0 and ≠0
-- ============================================================

/-- **T3** (non-vacuity). The holonomy observable provably attains both a nonzero value
    and zero: a computed holonomy carries information precisely because the observable
    is not constant. -/
theorem holonomy_non_vacuous :
    (∃ δ : Conn, holonomy δ ≠ 0) ∧ (∃ δ : Conn, holonomy δ = 0) := by
  refine ⟨⟨fun _ => 1, ?_⟩, ⟨fun _ => 0, ?_⟩⟩
  · rw [holonomy_const_one_eq_nine]; norm_num
  · simpa using holonomy_coboundary (fun _ => 0)

-- ============================================================
-- T4 — every coboundary connection is flat
-- ============================================================

/-- A connection is a *coboundary* iff it is induced by some layer-potential
    `g : Layer → ℤ` — i.e. it is the fiber displacement `g (transcend l) - g l`
    picked up along each edge. Since `transcend` acts as +1 mod 9, these are exactly
    the connections obtained by differencing a potential along the base. -/
def IsCoboundary (δ : Conn) : Prop := ∃ g : Layer → ℤ, ∀ l, δ l = g (transcend l) - g l

/-- **T4**. Every coboundary of a layer-potential is flat. Corollary of T2.

    Consequence: a *nonzero* holonomy can only arise from a connection that is NOT a
    coboundary (outside the coboundary subgroup) — i.e. from an explicitly added
    assumption, not derivable from the base cyclic structure alone. -/
theorem coboundary_is_flat (δ : Conn) (h : IsCoboundary δ) : holonomy δ = 0 := by
  obtain ⟨g, hg⟩ := h
  have hδ : δ = (fun l => g (transcend l) - g l) := funext hg
  rw [hδ]; exact holonomy_coboundary g

-- ============================================================
-- T5 — the dichotomy on two canonical connections
-- ============================================================

/-- The layer-index potential: a layer's value is its 0-based index. This is the
    canonical grading available from the base alone — the grade read off as a function
    of position on ℤ/9ℤ. -/
def layerIndexPotential : Layer → ℤ := fun l => (l.toNat : ℤ)

/-- The coboundary of the layer-index potential ("displacement = change in layer index"):
    the canonical coboundary connection. Its holonomy is *not* stipulated — it is forced
    once the connection is fixed, and is computed in T5a below. -/
def elevationFiber : Conn := fun l => layerIndexPotential (transcend l) - layerIndexPotential l

/-- **T5a (flat).** The coboundary of the layer-index potential has holonomy `0`:
    the single L9→L1 wrap-around step (−8) exactly cancels the eight unit ascents.
    Immediate from T2 (`holonomy_coboundary`) — the value was computed, not stipulated. -/
theorem elevationFiber_flat : holonomy elevationFiber = 0 := by
  unfold elevationFiber
  exact holonomy_coboundary layerIndexPotential

/-- **T5b (the winding connection is not a coboundary).** The constant-1 turn-counter
    connection (`+1` on every edge — the deck transformation of the universal cover
    `ℤ → ℤ/9ℤ`) is NOT a coboundary: no layer-potential generates it. Proof: if it were
    a coboundary it would be flat by T4, but its holonomy is `9 ≠ 0` (T1).

    Consequence: a *nonzero* holonomy provably requires a connection OUTSIDE the
    coboundary subgroup. Such a connection is an explicitly added assumption — it can
    never be derived from the base cyclic structure alone, which is why the canonical
    base-derived connection lands flat (T5a) while the winding connection must be
    supplied externally. -/
theorem spiral_not_coboundary : ¬ IsCoboundary (fun _ => (1 : ℤ)) := by
  intro h
  have hflat := coboundary_is_flat _ h
  rw [holonomy_const_one_eq_nine] at hflat
  norm_num at hflat

end CycleHolonomyWitness1
