# Ternary Impossibility

Formal verification proving that ternary operations satisfying cyclic symmetry, identity law, and weighted averaging necessarily have Lipschitz constant 3/2, causing exponential error amplification under
iteration. This generalizes to n-ary operations with Lipschitz constant n/(n-1) > 1 for all n≥3.

The result explains why Byzantine consensus protocols use median aggregation rather than arithmetic mean: median sidesteps the linear averaging axioms that force instability, achieving Lipschitz ≤1 and
the f<n/3 Byzantine tolerance bound.

Verified across four languages: Coq formalization with proofs and OCaml extraction, TLA+ temporal model checking, Wolfram numerical validation, and Python test suites covering federated learning, price
oracle manipulation, PDE stability, sensor fusion, and graph consensus.

Applications include distributed systems, Byzantine-resilient aggregation, DeFi oracle design, and robust signal processing.

**Experimental approach**: This project explores total characterization of Byzantine consensus limitations through algebraic axiomatization rather than protocol-level analysis. Instead of studying
specific consensus algorithms, we characterize the entire class of operations satisfying natural algebraic properties and prove impossibility results at the operator level. The multi-language verification
demonstrates that this alternative formulation produces consistent results across proof assistants, model checkers, and numerical methods.
