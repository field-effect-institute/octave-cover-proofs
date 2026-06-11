import Mathlib.Tactic
import OctaveCoverProofs.Layer
import OctaveCoverProofs.OctaveStructure
import OctaveCoverProofs.LayerCyclicityTypes
import OctaveCoverProofs.GradedOctaveCover

/-!
  ## LayerBaseIso — the two 9-cycle bases are one cyclic successor structure

  **What this discharges.** `GradedOctaveCover.lean` proves the graded-cover integration
  on the base type `LayerCyclicityTypes.Layer` (L1–L9, `transcend`). The `OctaveStructure`
  *class* instance, however, lives on a DIFFERENT carrier — `Layer.lean`'s `Layer`
  (L0–L8, `Layer.next`). The open question was the isomorphism between these two bases.
  This file closes it.

  **The iso.** Both carriers are the cyclic group ℤ/9ℤ with generator `+1`, sharing an index
  (`LayerCyclicityTypes.Layer.toNat`: L1↦0…L9↦8; `Layer.index`: L0↦0…L8↦8). The
  index-preserving relabel `baseEquiv` is an `Equiv` that **intertwines `transcend` with
  `Layer.next`** (`toOctaveBase_transcend`). Because the `OctaveStructure Layer` instance sets
  `next := Layer.next`, the first base is, up to this iso, the very cyclic base the
  `OctaveStructure` class runs on.

  **The payoff.** The cover projection transports across the iso: `projOct = baseEquiv ∘ proj`
  lands on the `OctaveStructure` carrier and still intertwines the integer successor with
  `Layer.next` (`projOct_succ`) and is octave-periodic (`projOct_periodic`). So the
  `OctaveStructure` base IS the degree-0 face of the same ℤ-graded cover — the integration
  result is not stranded on one carrier.

  **Still open (honest).** Whether a given concrete domain FORCES a real octave
  grade (vs. an observer merely counting loops) is untouched here; that per-domain question
  is answered in the instance files (`MusicOctaveGradedCover.lean`,
  `PeriodicTableGradedCover.lean`) and answered NO in `CosmoEpochsGradedCoverNegative.lean`.
-/

namespace LayerBaseIso

-- `Layer` (unqualified) = the OctaveStructure carrier from `Layer.lean` (L0–L8).
-- The other carrier is always written `LayerCyclicityTypes.Layer` in full.

/-- Forward base map: cyclicity base (L1–L9) → OctaveStructure base (L0–L8), by shared
    cyclic index (L1↦L0, …, L9↦L8). -/
def toOctaveBase : LayerCyclicityTypes.Layer → Layer
  | .L1 => .L0
  | .L2 => .L1
  | .L3 => .L2
  | .L4 => .L3
  | .L5 => .L4
  | .L6 => .L5
  | .L7 => .L6
  | .L8 => .L7
  | .L9 => .L8

/-- Inverse base map: OctaveStructure base (L0–L8) → cyclicity base (L1–L9). -/
def fromOctaveBase : Layer → LayerCyclicityTypes.Layer
  | .L0 => .L1
  | .L1 => .L2
  | .L2 => .L3
  | .L3 => .L4
  | .L4 => .L5
  | .L5 => .L6
  | .L6 => .L7
  | .L7 => .L8
  | .L8 => .L9

/-- **The base isomorphism.** The two 9-cycle carriers are equivalent as types. -/
def baseEquiv : LayerCyclicityTypes.Layer ≃ Layer where
  toFun := toOctaveBase
  invFun := fromOctaveBase
  left_inv := by intro l; cases l <;> rfl
  right_inv := by intro l; cases l <;> rfl

/-- The iso preserves the shared cyclic index: `toNat` on one side equals the
    OctaveStructure `index` of the image. The relabel is coordinate-faithful, not arbitrary. -/
theorem index_preserved (l : LayerCyclicityTypes.Layer) :
    (toOctaveBase l).index = l.toNat := by
  cases l <;> rfl

/-- **Intertwining (the load-bearing lemma).** The iso carries `transcend` to `Layer.next`:
    one step on one base becomes one step on the other. So the two cyclic successor
    structures are the same generator under `baseEquiv`. -/
theorem toOctaveBase_transcend (l : LayerCyclicityTypes.Layer) :
    toOctaveBase (LayerCyclicityTypes.transcend l) = (toOctaveBase l).next := by
  cases l <;> rfl

/-- The `OctaveStructure` class successor on `Layer` is exactly `Layer.next` (the instance
    sets `next := Layer.next`), so the intertwining holds against the class operation too. -/
theorem toOctaveBase_transcend_classNext (l : LayerCyclicityTypes.Layer) :
    toOctaveBase (LayerCyclicityTypes.transcend l)
      = OctaveStructure.next (toOctaveBase l) :=
  toOctaveBase_transcend l

-- ============================================================
-- TRANSPORTING THE COVER ONTO THE OctaveStructure CARRIER
-- ============================================================

/-- The cover projection, transported onto the `OctaveStructure` carrier: climb `n` cover
    rungs and read off the OctaveStructure-base layer. -/
def projOct (n : ℕ) : Layer := toOctaveBase (GradedOctaveCover.proj n)

/-- **Bundle commuting square on the OctaveStructure base.** `projOct` intertwines the integer
    successor with `Layer.next` — the OctaveStructure carrier is the degree-0 face of the cover. -/
theorem projOct_succ (n : ℕ) : projOct (n + 1) = (projOct n).next := by
  unfold projOct
  rw [GradedOctaveCover.proj_succ, toOctaveBase_transcend]

/-- The octave (`+9`) is the deck transformation on the OctaveStructure carrier too. -/
theorem projOct_periodic (n : ℕ) : projOct (n + 9) = projOct n := by
  unfold projOct
  rw [GradedOctaveCover.proj_periodic]

/-- `projOct` is surjective onto the OctaveStructure base (every layer hit within one octave). -/
theorem projOct_surjective (l : Layer) : ∃ n, n < 9 ∧ projOct n = l := by
  obtain ⟨n, hn, hl⟩ := GradedOctaveCover.proj_surjective (fromOctaveBase l)
  refine ⟨n, hn, ?_⟩
  unfold projOct
  rw [hl]
  cases l <;> rfl

-- ============================================================
-- THE KEYSTONE
-- ============================================================

/-- **The base-iso, assembled.** The cyclicity base and the `OctaveStructure`
    carrier are one cyclic successor structure (`baseEquiv`, intertwining `transcend` with
    `Layer.next`), and the ℤ-graded cover transports onto the `OctaveStructure` base:
    `projOct` intertwines the integer successor with `Layer.next`, is octave-periodic, and is
    surjective. The integration result therefore holds on the carrier the `OctaveStructure`
    class actually runs on — not only on the carrier it was first proved over. -/
theorem base_iso_intertwines :
    (∀ l, toOctaveBase (LayerCyclicityTypes.transcend l) = (toOctaveBase l).next) ∧
    (∀ l, (toOctaveBase l).index = l.toNat) ∧
    (∀ n, projOct (n + 1) = (projOct n).next) ∧
    (∀ n, projOct (n + 9) = projOct n) ∧
    (∀ l, ∃ n, n < 9 ∧ projOct n = l) := by
  exact ⟨toOctaveBase_transcend, index_preserved,
    projOct_succ, projOct_periodic, projOct_surjective⟩

end LayerBaseIso
