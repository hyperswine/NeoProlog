# Core operand slots and tail frames

The Core driver can reuse a clause activation for a final ordinary predicate
call. This recycles heap-resident operand slots, alongside the continuation
reuse already present in the driver. It does not allocate a separate native
stack, color variable lifetimes within a clause, or change source algorithms.

## Local operands and stable variables

An activation slot holds a value. Call arguments, constructor fields and other
escaping operands receive that value rather than a reference to its storage.
Reading a still-unbound local for one of these uses promotes it to a separate
stable heap variable and redirects the slot to it. Promotion preserves the
logical variable ID and does not advance the fresh-variable supply. Numeric
`is` targets can be bound directly because a number cannot retain a pointer to
its target slot.

Clause compilation records the slots requiring initialization. First head
occurrences write their slots directly; construction against an unbound
incoming argument initializes first occurrences in head traversal order.
Other local slots start unbound. Both new and recycled frames use this layout.

Physical addresses cease to indicate logical variable age. Variable-variable
unification therefore chooses its representative by logical ID. Fresh IDs
still advance by the original clause variable count, including the existing
one-ID reservation for zero-variable clauses. A recycled frame may have excess
capacity; those unused offsets are inaccessible to the new clause.

## Reuse boundary

The outgoing arguments must be materialized before overwrite. Reuse also
requires a single selected clause, sufficient frame capacity, a final call,
and no surviving continuation that uses the frame. Its marker must be at or
above the newest choice point's heap mark. A call-boundary collection
invalidates the offered frame; detached plans retain their relocated `PWord`
references. Tabled continuations conservatively prevent reuse.

Promotion uses ordinary trailed bindings, so alternatives restore the operand
before reclaiming its promoted variable. Stable variable cells remain visible
to constraint watches, copied results, output checks and exported answers.
Resetting a proven-dead frame does not rewind the heap over escaped terms.

The continuation check relies on allocation order: a new activation is above
its callers, and in-place tail reuse preserves that order. The first older,
nonempty caller proves its ancestors also predate the candidate. A future
allocator that recycles arbitrary frames from a free list must revisit this
shortcut. The head occurs check uses fresh logical identity, rather than
physical address age, to exclude first-occurrence variables.

## Evidence and limits

`CoreSlotsTest` compares native execution with Reference at initial collection
limits 1, 16 and the default. It checks ordered events, exact projected variable
IDs, freshness, residuals, output and errors. Generated cases cover reverse,
escaping aliases and changing frame widths. Fixtures exercise control scopes,
failed heads, constraints, tables, dynamic facts and retained answers.

Optional `runCoreWithSlotStats` counters record allocated activation frames,
reused tail frames and reused slot cells. Normal execution disables these
per-clause counters. Tests require substantial reuse in a long ground loop,
reuse in reverse, and refusal while a same-frame alternative survives.

Frame reuse can bound activation storage in a ground tail loop. Escaping
variables and constructed terms still allocate; non-tail recursion still
retains callers. Fewer allocations can also mean fewer collection opportunities.
The existing dead-graph test now adds explicit temporary-term pressure rather
than assuming a ground spin must allocate frames.

See the [profile and benchmark report](2026-10-18-ENGINE-SLOTS.md)
for measured CPU and allocation results. Logical Core cell storage, GHC
allocation and whole-process residency are separate measurements.
