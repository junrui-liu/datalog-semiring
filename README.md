# Fun with Semirings /\ Datalog

- [lib/s.ml](lib/s.ml) contains a simple (almost verbatim) implementation of Dolan's *Fun with Semirings* paper, including the matrix semiring and the closure operator.
- [lib/datalog.ml](lib/datalog.ml) contains a simple implementation of Datalog-over-semiring and naive evaluation. Convergence is not guaranteed, even if the underlying semiring is closed.