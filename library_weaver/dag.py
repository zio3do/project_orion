"""
DAG Walker — topological traversal of the execution plan with failure propagation.

Walks planned entries in order_index order (which is a topological sort
from the Library Architect's assembler). Tracks per-entry status and
propagates failures: when an entry fails, all its transitive dependents
are marked "skipped".

The walker is the only component that decides whether an entry should be
attempted or skipped. The weaver core asks ``next_entry()`` and acts on
the result.
"""

from __future__ import annotations

from library_weaver.models import PlannedEntry, WeavePlan


class DAGWalker:
    """Walks planned entries in topological order, propagating failures.

    Statuses:
        pending  — not yet processed
        done     — proved successfully
        failed   — Oracle returned False or raised an exception
        skipped  — a transitive dependency failed
    """

    def __init__(
        self,
        plan: WeavePlan,
        pre_done: frozenset[str] | None = None,
    ) -> None:
        self._entries: tuple[PlannedEntry, ...] = plan.entries
        self._dag: dict[str, tuple[str, ...]] = plan.dag
        self._status: dict[str, str] = {e.name: "pending" for e in plan.entries}
        self._skip_reasons: dict[str, str] = {}
        self._cursor: int = 0

        # Build reverse DAG: name → set of direct dependents
        self._dependents: dict[str, set[str]] = {e.name: set() for e in plan.entries}
        for name, deps in self._dag.items():
            for dep in deps:
                if dep in self._dependents:
                    self._dependents[dep].add(name)

        # Pre-mark entries from a previous run as done (resume support).
        # Only marks entries that actually exist in the plan.
        if pre_done:
            for name in pre_done:
                if name in self._status:
                    self._status[name] = "done"

    def next_entry(self) -> PlannedEntry | None:
        """Return the next entry to process, or None if all entries are done.

        Automatically advances past entries that have already been resolved
        (done, failed, or skipped).
        """
        while self._cursor < len(self._entries):
            entry = self._entries[self._cursor]
            if self._status[entry.name] == "pending":
                return entry
            self._cursor += 1
        return None

    def advance(self) -> None:
        """Move the cursor past the current entry after processing."""
        self._cursor += 1

    def mark_done(self, name: str) -> None:
        """Mark an entry as successfully proven."""
        self._status[name] = "done"

    def mark_failed(self, name: str) -> None:
        """Mark an entry as failed and skip all transitive dependents."""
        self._status[name] = "failed"
        self._propagate_skip(name)

    def status(self, name: str) -> str:
        """Return the current status of an entry."""
        return self._status[name]

    def skip_reason(self, name: str) -> str:
        """Return the skip reason for an entry, or empty string."""
        return self._skip_reasons.get(name, "")

    def summary(self) -> dict[str, int]:
        """Return counts by status: done, failed, skipped, pending."""
        counts = {"done": 0, "failed": 0, "skipped": 0, "pending": 0}
        for s in self._status.values():
            counts[s] += 1
        return counts

    def _propagate_skip(self, failed_name: str) -> None:
        """Mark all transitive dependents of `failed_name` as skipped.

        Uses BFS over the reverse DAG to find all entries reachable
        from the failed entry.
        """
        queue = list(self._dependents.get(failed_name, set()))
        visited: set[str] = set()

        while queue:
            name = queue.pop(0)
            if name in visited:
                continue
            visited.add(name)

            if self._status[name] == "pending":
                self._status[name] = "skipped"
                self._skip_reasons[name] = f"dependency failed: {failed_name}"

            # Continue propagation through this node's dependents
            for dep in self._dependents.get(name, set()):
                if dep not in visited:
                    queue.append(dep)
