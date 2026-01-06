
### 1. Stability under conversion and metasubstitution

Elaboration must not distinguish convertible terms.

Elaboration must be stable under metasubstitution. This is a weaker form of stability. It means that
if we reorder elaboration actions and metavariable solutions, the *eventual* output must not change,
up to conversion.

### 2. Re-checkability

Every core term contained in interaction output must be printable in a form which is re-checkable in
the scope of the interaction.

EDIT: we might want to soften this requirement to *meta-free* terms. Re-checking metas isn't
too horrible, because we could convert them to let-bindings + fresh metas. But if we want to also
re-check *postponed defn equalities*, that's rather problematic to support in user-facing syntax.
The simplest design is to not support any meta stuff in user-facing syntax.

### 3. Partial output instead of hard failure

Elaboration does not fail, instead it accummulates errors and represents hard failures as
partial output, i.e. metavariables in output. The output should be defined as much as possible.
