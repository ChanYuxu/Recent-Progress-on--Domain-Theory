import PointCentralFubini.SecondCountable
import PointCentralFubini.Normalization
import PointCentralFubini.Fatou
import PointCentralFubini.OuterTrace
import PointCentralFubini.SorgenfreyFubini

/-!
Main source-facing entry points:
* `countable_fubini`: source corollary 3.3.
* `second_countable_fubini`: source corollary 5.4.
* `extremal_observables` and `sorgenfrey_inner_skeleton`: source Lemmas 4.5 and 4.6.
* `measure_source_incidence`: source Proposition 4.2.
* `full_vietoris_lift`: source Lemma 4.4.
* `sorgenfrey_fubini`: source Theorem 4.7, without manuscript-internal hypotheses.
  The earlier conditional wrappers remain available for compatibility.

Registered literature axioms are still explicit proof dependencies.
The source ledger, environment audit and pending review are part of the deliverable.
-/
