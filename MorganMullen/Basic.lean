import MorganMullen.NT
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Morgan–Mullen conjecture: basic definitions

This file fixes the notions used in the statement of the conjecture.

* `IsNormalElem K E w`   : `w` is normal over `K`, i.e. its `Gal(E/K)`-conjugates form a `K`-basis of `E`.
* `IsCompletelyNormal F E w` : `w` is normal over every intermediate field `F ⊆ K ⊆ E`
  (for finite fields these are exactly the `𝔽_{q^d}`, `d ∣ n`).
* `IsPrimitiveElem w`    : `w` generates the multiplicative group `Eˣ`.
* `HasMMProperty F E`    : `E` contains a primitive completely normal element over `F`.

Reference: F. Hellwig, *Resolvent Components of Completely Normal Elements and the Morgan–Mullen Conjecture*, arXiv
preprint (2026). Numbers such as "Lemma 2.3" and notation such as `ℰ`, `𝒞`, `w_𝒞`, `σ_1`, `κ_3`, `ϑ`
refer to that paper.
-/

namespace MorganMullen

section FieldDefs

/-- `w ∈ E` is *normal* over `K`: the family of its conjugates `σ w`, `σ ∈ Gal(E/K)`, is a `K`-basis
of `E` (it is linearly independent and spans `E`). -/
def IsNormalElem (K E : Type*) [Field K] [Field E] [Algebra K E] (w : E) : Prop :=
  LinearIndependent K (fun σ : Gal(E/K) => σ w) ∧
    Submodule.span K (Set.range fun σ : Gal(E/K) => σ w) = ⊤

/-- `w ∈ E` is *completely normal* over `F`: it is normal over every intermediate field
`F ⊆ K ⊆ E`. For `E = 𝔽_{q^n}`, `F = 𝔽_q` these are the fields `𝔽_{q^d}`, `d ∣ n`. -/
def IsCompletelyNormal (F E : Type*) [Field F] [Field E] [Algebra F E] (w : E) : Prop :=
  ∀ K : IntermediateField F E, IsNormalElem K E w

/-- `w ∈ E` is *primitive*: it is non-zero and every non-zero element of `E` is a power of `w`,
i.e. `w` generates the cyclic group `Eˣ`. -/
def IsPrimitiveElem {E : Type*} [Field E] (w : E) : Prop :=
  w ≠ 0 ∧ ∀ x : E, x ≠ 0 → ∃ k : ℕ, w ^ k = x

/-- The *Morgan–Mullen property* of the extension `E/F`: `E` contains an element that is primitive
and completely normal over `F`. -/
def HasMMProperty (F E : Type*) [Field F] [Field E] [Algebra F E] : Prop :=
  ∃ w : E, IsPrimitiveElem w ∧ IsCompletelyNormal F E w

end FieldDefs



end MorganMullen
