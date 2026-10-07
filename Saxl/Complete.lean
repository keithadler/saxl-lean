import Mathlib
import Saxl.Statement
import Saxl.OAI.Main

/-!
# Saxl's conjecture, closed using OpenAI's vendored proof

`Saxl/OAI/` is OpenAI's own Lean proof of the paper (vendored verbatim from `openai/math`, commit
`adc7f12`, Apache-2.0, with the namespace renamed to `OAI.SaxlOAI` to avoid clashes).  Its
`Model.lean` is byte-identical to the challenge definitions in `Saxl/Statement.lean` (minus the
`sorry`ed theorem), so their final theorem is *definitionally* a proof of the challenge statement.
This file records that bridge; nothing here is proved by this repository.
-/

namespace OAI.Saxl

/-- **Saxl's conjecture**, in the challenge's own terms, obtained from OpenAI's vendored proof.
The two `SaxlConjecture` definitions unfold to the same term. -/
theorem saxl_conjecture_vendored : SaxlConjecture := OAI.SaxlOAI.saxl_conjecture

end OAI.Saxl
