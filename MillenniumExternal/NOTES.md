# Direct adapter semantics

A direct adapter is considered closed only when a theorem term typechecks
against the exact pinned upstream proposition. Matching names, status booleans,
module imports, or mathematical prose are not sufficient.

This branch intentionally keeps the adapter receipts RED-TYPE until that
cross-package theorem term exists. This is the mechanism that turns the next
kernel run into a gap detector rather than a success-label generator.
